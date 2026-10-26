/*
Copyright 2026

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

*/

//
// Remote printing. Installs a virtual printer on this device whose output is captured by the agent.
// The printer is pointed at a raw TCP socket on 127.0.0.1 that this module listens on, every connection
// is one print job. The job is saved to disk and handed to the caller so it can be downloaded by the user.
//
// Windows: "Microsoft Print To PDF" driver on a Standard TCP/IP port, the spooler sends the PDF to us.
// Linux:   CUPS queue with a PPD that converts to PDF, using the "socket://" backend.
//

var fs = require('fs');

var PORT_PREFIX = 'MeshCentralPrint';               // Windows printer port name prefix, used to find our printers
var DEFAULT_PRINTER_NAME = 'MeshCentral Printer';
var DEFAULT_TCP_PORT = 35500;
var MAX_JOB_SIZE = 256 * 1024 * 1024;               // Larger jobs are dropped
var MAX_JOB_AGE = 15 * 60 * 1000;                   // Jobs older than this are deleted

var sep = (process.platform == 'win32') ? '\\' : '/';
var agentFolder = process.execPath.substring(0, process.execPath.lastIndexOf(sep));
var jobsFolder = agentFolder + sep + 'PrintJobs';
var markerFile = agentFolder + sep + 'remoteprinter.json'; // Present while a printer is installed, so leftovers can be removed
var ppdFile = agentFolder + sep + 'remoteprinter.ppd';

var server = null;          // TCP listener receiving print jobs
var current = null;         // { name, port } of the installed printer
var jobCounter = 0;
var children = [];          // Keep a reference on running child processes
var queue = [];             // Install / uninstall operations run one at a time
var queueBusy = false;

// Minimal PPD, CUPS converts the job to PDF and sends it as-is to the socket backend
var linuxPpd = [
    '*PPD-Adobe: "4.3"',
    '*FormatVersion: "4.3"',
    '*FileVersion: "1.0"',
    '*LanguageVersion: English',
    '*LanguageEncoding: ISOLatin1',
    '*PCFileName: "MESHPDF.PPD"',
    '*Manufacturer: "MeshCentral"',
    '*Product: "(MeshCentral Remote Printer)"',
    '*ModelName: "MeshCentral Remote Printer"',
    '*ShortNickName: "MeshCentral Remote Printer"',
    '*NickName: "MeshCentral Remote Printer, PDF"',
    '*PSVersion: "(3010.000) 0"',
    '*LanguageLevel: "3"',
    '*ColorDevice: True',
    '*DefaultColorSpace: RGB',
    '*FileSystem: False',
    '*Throughput: "1"',
    '*LandscapeOrientation: Plus90',
    '*TTRasterizer: Type42',
    '*cupsVersion: 2.2',
    '*cupsFilter2: "application/vnd.cups-pdf application/pdf 0 -"',
    '*OpenUI *PageSize/Media Size: PickOne',
    '*OrderDependency: 10 AnySetup *PageSize',
    '*DefaultPageSize: Letter',
    '*PageSize Letter/US Letter: "<</PageSize[612 792]>>setpagedevice"',
    '*PageSize Legal/US Legal: "<</PageSize[612 1008]>>setpagedevice"',
    '*PageSize A4/A4: "<</PageSize[595 842]>>setpagedevice"',
    '*CloseUI: *PageSize',
    '*OpenUI *PageRegion: PickOne',
    '*OrderDependency: 10 AnySetup *PageRegion',
    '*DefaultPageRegion: Letter',
    '*PageRegion Letter/US Letter: "<</PageSize[612 792]>>setpagedevice"',
    '*PageRegion Legal/US Legal: "<</PageSize[612 1008]>>setpagedevice"',
    '*PageRegion A4/A4: "<</PageSize[595 842]>>setpagedevice"',
    '*CloseUI: *PageRegion',
    '*DefaultImageableArea: Letter',
    '*ImageableArea Letter/US Letter: "0 0 612 792"',
    '*ImageableArea Legal/US Legal: "0 0 612 1008"',
    '*ImageableArea A4/A4: "0 0 595 842"',
    '*DefaultPaperDimension: Letter',
    '*PaperDimension Letter/US Letter: "612 792"',
    '*PaperDimension Legal/US Legal: "612 1008"',
    '*PaperDimension A4/A4: "595 842"',
    ''
].join('\n');

function isSupported() { return (process.platform == 'win32') || ((process.platform == 'linux') && (getLpadmin() != null)); }

function getLpadmin() {
    var paths = ['/usr/sbin/lpadmin', '/usr/bin/lpadmin', '/sbin/lpadmin'];
    for (var i in paths) { if (fs.existsSync(paths[i])) return paths[i]; }
    return null;
}

// Make the printer name safe for the platform
function cleanName(name) {
    if ((typeof name != 'string') || (name.length == 0)) { name = DEFAULT_PRINTER_NAME; }
    name = name.replace(/[\x00-\x1F\x7F]/g, '').substring(0, 64);
    if (process.platform == 'win32') { name = name.replace(/[\\,!]/g, '_'); } else { name = name.replace(/[\s\/#\\'"]/g, '_'); }
    if (name.trim().length == 0) { name = (process.platform == 'win32') ? DEFAULT_PRINTER_NAME : DEFAULT_PRINTER_NAME.replace(/ /g, '_'); }
    return name.trim();
}

function psQuote(str) { return "'" + str.replace(/'/g, "''") + "'"; }

// Run a queued operation, operations are run one at a time
function runQueued(func) {
    queue.push(func);
    if (queueBusy == false) { runNext(); }
}
function runNext() {
    if (queue.length == 0) { queueBusy = false; return; }
    queueBusy = true;
    var func = queue.shift();
    try { func(runNext); } catch (ex) { runNext(); }
}

// Run a PowerShell script, callback(exitCode, output)
function runPowerShell(script, func) {
    var psPath = (process.env['SystemRoot'] || 'C:\\Windows') + '\\System32\\WindowsPowerShell\\v1.0\\powershell.exe';
    var child = require('child_process').execFile(psPath, ['powershell', '-NoProfile', '-NoLogo', '-NonInteractive', '-ExecutionPolicy', 'Bypass', '-Command', '-'], {});
    children.push(child);
    child.stdout.str = ''; child.stderr.str = '';
    child.stdout.on('data', function (c) { this.str += c.toString(); });
    child.stderr.on('data', function (c) { this.str += c.toString(); });
    child.on('exit', function (code) {
        var i = children.indexOf(child); if (i >= 0) { children.splice(i, 1); }
        func(code, (child.stdout.str + child.stderr.str).trim());
    });
    child.stdin.write(script + '\r\nexit $LASTEXITCODE\r\n');
}

// Run a command without a shell, callback(exitCode, output)
function runCommand(path, args, func) {
    var child = require('child_process').execFile(path, args);
    children.push(child);
    child.stdout.str = ''; child.stderr.str = '';
    child.stdout.on('data', function (c) { this.str += c.toString(); });
    child.stderr.on('data', function (c) { this.str += c.toString(); });
    child.on('exit', function (code) {
        var i = children.indexOf(child); if (i >= 0) { children.splice(i, 1); }
        func(code, (child.stdout.str + child.stderr.str).trim());
    });
}

function readMarker() { try { return JSON.parse(fs.readFileSync(markerFile).toString()); } catch (ex) { return null; } }
function writeMarker(m) { try { fs.writeFileSync(markerFile, JSON.stringify(m)); } catch (ex) { } }
function deleteMarker() { try { fs.unlinkSync(markerFile); } catch (ex) { } }

// Install the printer, callback(err)
function installPrinter(name, port, func) {
    if (process.platform == 'win32') {
        var portName = PORT_PREFIX + '_' + port;
        var script = [
            "$ErrorActionPreference = 'Stop'",
            "try {",
            "  $name = " + psQuote(name) + "; $port = " + psQuote(portName) + "; $drv = 'Microsoft Print To PDF'",
            "  if (-not (Get-PrinterDriver -Name $drv -ErrorAction SilentlyContinue)) { throw ('Printer driver not found: ' + $drv) }",
            "  $existing = Get-Printer -Name $name -ErrorAction SilentlyContinue",
            "  if ($existing -and ($existing.PortName -notlike '" + PORT_PREFIX + "*')) { throw ('A printer with this name already exists: ' + $name) }",
            "  Get-Printer | Where-Object { ($_.PortName -like '" + PORT_PREFIX + "*') -and (($_.Name -ne $name) -or ($_.PortName -ne $port)) } | Remove-Printer",
            "  if (-not (Get-PrinterPort -Name $port -ErrorAction SilentlyContinue)) { Add-PrinterPort -Name $port -PrinterHostAddress '127.0.0.1' -PortNumber " + port + " }",
            "  if (-not (Get-Printer -Name $name -ErrorAction SilentlyContinue)) { Add-Printer -Name $name -DriverName $drv -PortName $port }",
            "  Write-Output 'OK'",
            "} catch { Write-Output $_.Exception.Message; exit 1 }"
        ].join('\r\n');
        runPowerShell(script, function (code, output) { func(((code == 0) && (output.indexOf('OK') >= 0)) ? null : (output || 'PowerShell error')); });
    } else if (process.platform == 'linux') {
        var lpadmin = getLpadmin();
        if (lpadmin == null) { func('CUPS is not installed (lpadmin not found)'); return; }
        try { fs.writeFileSync(ppdFile, linuxPpd); } catch (ex) { func('Unable to write PPD file'); return; }
        // If the printer name changed, remove the old queue first
        var marker = readMarker();
        var removeOld = function (next) { if ((marker != null) && (marker.name != null) && (marker.name != name)) { runCommand(lpadmin, ['lpadmin', '-x', marker.name], function () { next(); }); } else { next(); } };
        removeOld(function () {
            runCommand(lpadmin, ['lpadmin', '-p', name, '-E', '-v', 'socket://127.0.0.1:' + port, '-P', ppdFile, '-D', 'MeshCentral Remote Printer', '-o', 'printer-is-shared=false'], function (code, output) {
                func((code == 0) ? null : (output || ('lpadmin error ' + code)));
            });
        });
    } else {
        func('Remote printing is not supported on this platform');
    }
}

// Remove all printers installed by this module, callback()
function uninstallPrinter(func) {
    var marker = readMarker();
    if (process.platform == 'win32') {
        var script = [
            "$ErrorActionPreference = 'SilentlyContinue'",
            "Get-Printer | Where-Object { $_.PortName -like '" + PORT_PREFIX + "*' } | Remove-Printer",
            "Start-Sleep -Milliseconds 500",
            "Get-PrinterPort | Where-Object { $_.Name -like '" + PORT_PREFIX + "*' } | Remove-PrinterPort",
            "Write-Output 'OK'"
        ].join('\r\n');
        runPowerShell(script, function () { deleteMarker(); func(); });
    } else if (process.platform == 'linux') {
        var lpadmin = getLpadmin();
        if ((lpadmin == null) || (marker == null) || (marker.name == null)) { deleteMarker(); func(); return; }
        runCommand(lpadmin, ['lpadmin', '-x', marker.name], function () { try { fs.unlinkSync(ppdFile); } catch (ex) { } deleteMarker(); func(); });
    } else {
        deleteMarker(); func();
    }
}

// Delete old jobs. If all is true, delete all of them.
function cleanJobs(all) {
    var files = null;
    try { files = fs.readdirSync(jobsFolder); } catch (ex) { return; }
    var now = Date.now();
    for (var i in files) {
        var m = /^print-(\d+)-/.exec(files[i]);
        if ((all === true) || (m == null) || ((now - parseInt(m[1])) > MAX_JOB_AGE)) { try { fs.unlinkSync(jobsFolder + sep + files[i]); } catch (ex) { } }
    }
}

// Figure out the file extension from the first bytes of the job
function getJobExtension(head) {
    var str = head.toString('binary');
    if (str.indexOf('%PDF') >= 0) return 'pdf';
    if (str.indexOf('%!PS') >= 0) return 'ps';
    if ((head.length >= 2) && (head[0] == 0x50) && (head[1] == 0x4B)) return 'xps';
    return 'prn';
}

function startListener(port, onJob, func) {
    if (server != null) { func(null); return; }
    try { fs.mkdirSync(jobsFolder); } catch (ex) { }
    var s = require('net').createServer();
    s.on('connection', function (socket) {
        var job = { id: ++jobCounter, time: Date.now(), size: 0, head: null, fd: null, done: false };
        job.tmpPath = jobsFolder + sep + 'print-' + job.time + '-' + job.id + '.tmp';
        try { job.fd = fs.openSync(job.tmpPath, 'wbN'); } catch (ex) { socket.end(); return; }
        socket.on('data', function (chunk) {
            if ((job.done) || (job.fd == null)) return;
            if (job.head == null) { job.head = Buffer.from(chunk.slice(0, 1024)); }
            job.size += chunk.length;
            if (job.size > MAX_JOB_SIZE) { try { fs.closeSync(job.fd); } catch (ex) { } job.fd = null; try { fs.unlinkSync(job.tmpPath); } catch (ex) { } socket.end(); return; }
            try { fs.writeSync(job.fd, chunk); } catch (ex) { }
        });
        var finish = function () {
            if (job.done) return;
            job.done = true;
            if (job.fd == null) return; // Job was dropped
            try { fs.closeSync(job.fd); } catch (ex) { }
            if (job.size == 0) { try { fs.unlinkSync(job.tmpPath); } catch (ex) { } return; }
            var ext = getJobExtension(job.head);
            var name = 'print-' + job.time + '-' + job.id + '.' + ext;
            var path = jobsFolder + sep + name;
            try { fs.renameSync(job.tmpPath, path); } catch (ex) { path = job.tmpPath; name = 'print-' + job.time + '-' + job.id + '.tmp'; }
            cleanJobs(false);
            try { onJob({ path: path, name: name, size: job.size, format: ext }); } catch (ex) { }
        };
        socket.on('end', finish);
        socket.on('close', finish);
        socket.on('error', finish);
    });
    s.on('error', function (err) { });
    try {
        s.listen({ port: port, host: '127.0.0.1' });
    } catch (ex) {
        func('Unable to listen on port ' + port);
        return;
    }
    server = s;
    func(null);
}

function stopListener() {
    if (server == null) return;
    try { server.close(); } catch (ex) { }
    server = null;
}

// Start remote printing. options: { printerName, port }, onJob({ path, name, size, format }), func(err, { name, port })
function start(options, onJob, func) {
    if (options == null) { options = {}; }
    var name = cleanName(options.printerName);
    var port = parseInt(options.port);
    if (isNaN(port) || (port < 1024) || (port > 65535)) { port = DEFAULT_TCP_PORT; }
    runQueued(function (done) {
        if (isSupported() == false) { func('Remote printing is not supported on this device'); done(); return; }
        if ((current != null) && (current.name == name) && (current.port == port) && (server != null)) { func(null, current); done(); return; } // Already running
        if ((current != null) && (current.port != port)) { stopListener(); }
        startListener(port, onJob, function (err) {
            if (err != null) { func(err); done(); return; }
            installPrinter(name, port, function (err) {
                if (err != null) {
                    stopListener();
                    current = null;
                    uninstallPrinter(function () { func(err); done(); });
                    return;
                }
                current = { name: name, port: port };
                writeMarker(current);
                func(null, current);
                done();
            });
        });
    });
}

// Stop remote printing, remove the printer and pending jobs. func() is optional.
function stop(func) {
    runQueued(function (done) {
        stopListener();
        current = null;
        uninstallPrinter(function () {
            cleanJobs(true);
            if (func) { try { func(); } catch (ex) { } }
            done();
        });
    });
}

// Remove a printer left behind by a previous run (agent crash or restart while printing was active)
function cleanup() {
    if (readMarker() != null) { stop(); } else { cleanJobs(true); }
}

function isRunning() { return (current != null); }

module.exports = { start: start, stop: stop, cleanup: cleanup, isRunning: isRunning, isSupported: isSupported, jobsFolder: jobsFolder };
