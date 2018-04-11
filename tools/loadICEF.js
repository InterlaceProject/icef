/*
 * loadICEF.js v1.0
 *
 * This file contains source code developed by the European
 * FP7 research project BIOMICS (Grant no. 318202)
 * Copyright (C) 2016 Daniel Schreckling
 *
 * Licensed under the Academic Free License version 3.0
 *   http://www.opensource.org/licenses/afl-3.0.php
 *
 *
 */

var jsonfile = require('jsonfile');
var http = require("http");
var fs = require("fs");
var path = require("path");

if (process.argv.length < 5) {
	console.log("Error: Invalid number of arguments");
	console.log("Usage: nodejs load.js SPEC HOST PORT");
	console.log("\tSPEC\tpath to file containing the ICEF specification to load");
	console.log("\tHOST\thostname or IP of CoreASIM manager");
	console.log("\tPORT\tport of CoreASIM manager");
	return -1;
}

var specification = process.argv[2];
var trgHost = process.argv[3];
var trgPort = process.argv[4];

function reloadJSON(icef, baseDir) {
	var toload = [];

	for (var prop in icef) {
		switch (prop) {
			case "asims" :
			case "schedulers" :
				var asims = icef[prop];
				if (!(asims instanceof Array)) {
					console.log("Invalid ICEF specification. Expected array of ASIM specifications in '" + prop + "'.");
				} else {
					for (var i in asims) {
						var asim = asims[i];
						if (asim != undefined && asim.file != undefined) {
							toload.push({file: asim.file, index: i, prop: prop, start: asim.start, include: asim.include});
						}
					}
				}
				break;
		}
	}

	for (var i in toload) {
		var file = toload[i].file;
		var incl = toload[i].include;
		var index = toload[i].index;
		var prop = toload[i].prop;
		var start = toload[i].start;

		if (file[0] != "/") {
			file = baseDir + "/" + file;
		}
		data = new String(fs.readFileSync(file));

		//eh: added include property for ICEF json String
		//    to compensate for the non-working Modularity
		if (incl != undefined && incl != null && incl instanceof Array) {
			//process each file from include array
			incl.forEach(function (f) {
				var inclFile = f;
				//append baseDir if necessary
				if (inclFile[0] != "/") {
					inclFile = baseDir + "/" + inclFile;
				}
				//load file from fs and replace dummy code
				var dataIncl = new String(fs.readFileSync(inclFile));
				dataIncl =
					dataIncl.replace(
						/\/\*includeskip begin\*\/(.|[\r\n])+\/*includeskip end\*\//m,
						"");
				//append to content of main file
				data += "\r\n" + dataIncl;
			});
		}

		if (data == null) {
			return null;
		} else {
			var newASIM = {};

			data = data.replace(/\/\/.+/g, "");
			data = data.replace(/[ \r\n]*use .+/g, "");

			var match = /[ \r\n]*CoreASIM ([^\r\n]+)[\r\n]+/g.exec(data);
			if (match === null || match[1] === null)
				newASIM.name = "undefined";
			else
				newASIM.name = match[1];

			match = /[ \r\n]*init ([^\r\n]+)[\r\n]+/g.exec(data);
			if (match === null || match[1] === null)
				newASIM.init = "skip";
			else
				newASIM.init = match[1];

			match = /[ \r\n]*scheduling ([^\r\n]+)[\r\n]+/g.exec(data);
			if (match === null || match[1] === null)
				newASIM.policy = "skip";
			else {
				newASIM.policy = match[1];
			}

			// guess the init rule and extract program(self)
			var initRuleExp = new RegExp("rule[ \t]+" + newASIM.init + ".*=(.|[\n\r])+?(rule|derived|controlled|universe)", "m");
			var initRule = null;
			match = initRuleExp.exec(data);
			if (match === null)
				initRule = null;
			else
				initRule = match[0];

			match = /program\(self\) *:= *([^\r\n]+?)[\r\n]+/g.exec(initRule);
			if (match === null || match[1] === null)
				newASIM.program = "skip";
			else
				newASIM.program = match[1];

			data = data.replace(/[ \r\n]*CoreASIM ([^ \r\n]+)[\r\n]+/g, "\r\n");
			data = data.replace(/[ \r\n]*init ([^ \r\n]+)[\r\n]+/g, "\r\n");
			data = data.replace(/[ \r\n]*scheduling ([^\r\n]+)[\r\n]+/g, "\r\n");
			data = data.replace(/^( |\r\n)*/m, "");
			data = data.replace(/( |\r\n)*$/m, "");

			newASIM.signature = data;

			if (start != undefined)
				newASIM.start = start;

			icef[prop][index] = newASIM;
		}
	}

	return icef;
}

jsonfile.readFile(specification, function (err, icef) {
	if (err != null) {
		console.log("Error: " + err);
	} else {
		var baseDir = path.dirname(specification);

		var newICEF = reloadJSON(icef, baseDir);
		var data = JSON.stringify(icef);

		var options = {
			host: trgHost,
			port: trgPort,
			path: '/simulations',
			method: 'PUT',
			headers: {
				'Content-Type': 'application/json',
				'Content-Length': Buffer.byteLength(data)
			}
		};

		var self = this;
		var req = http.request(options, function (res) {
			var resData = "";

			res.setEncoding('utf8');

			res.on('data', function (chunk) {
				if (chunk)
					resData += chunk;
			});

			// TODO: create error in brapper which shows that something went wrong
			res.on('end', function (chunk) {
				if (chunk)
					resData += chunk;

				if (res.statusCode != 201) {
					console.log("Specification not loaded!");
					console.log("Problem: ", resData);
				} else {
					var result = null;
					try {
						result = JSON.parse(resData);
						console.log("Specification loaded successfully.");
					} catch (e) {
						console.log("Unexpected response from manager: " + resData);
					}
				}
			});
		});

		req.on('error', function (e) {
			console.log("Unable to load ICEF specifiation: " + e);
		});

		req.write(data);
		req.end();
	}
});
