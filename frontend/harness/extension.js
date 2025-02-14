// Import the module and reference it with the alias vscode in your code below
const vscode = require('vscode');
const fs = require('fs');
const path = require('path');
const { spawn, execSync } = require("child_process");
const { parseProject } = require('./callGraph.js');
const { extractFunctionCode } = require('./parserCore.js');

// function to get directory Tree structure of current wd (reference for error logging context later on)
function getDirectoryTree(dirPath, options = {}) {
	const {
		ignore = ['.git', 'node_modules'],
		maxDepth = Infinity,
		currentDepth = 0
	} = options;
	let tree = '';
	try {
		if (currentDepth >= maxDepth) return tree;
		const items = fs.readdirSync(dirPath)
			.filter(item => !ignore.includes(item));
		items.forEach((item, index) => {
			const fullPath = path.join(dirPath, item);
			const isLast = index === items.length - 1;
			const prefix = '  '.repeat(currentDepth) + (isLast ? '└── ' : '├── ');
			try {
				const stats = fs.statSync(fullPath);
				tree += prefix + item + '\n';

				if (stats.isDirectory()) {
					tree += getDirectoryTree(fullPath, {
						...options,
						currentDepth: currentDepth + 1
					});
				}
			} catch (err) {
				console.error(`Error processing ${fullPath}: ${err.message}`);
			}
		});
		return tree;
	} catch (err) {
		console.error(`Error reading directory ${dirPath}: ${err.message}`);
		return tree;
	}
}

// function for input specified function on currently opened .c file by user
function readCFile(workspacePath, cProjectDir, function_name) {
	let context;
	// invoke callGraph function
	try {
		context = parseProject(workspacePath);
		// returns the following:
		// console.log(context.functionMap); // {function name: absolute path}
		// console.log(context.callMatrix); // {function name: {invoked function: number of times invoked}}
		// console.log(context.adjacencyMatrix); // {matrix containing call matrix in graph form}
		// console.log(context.functionIndex); // {function name: index} (to reference adjacencyMatrix)
		// console.log(context.allFunctions); // [all functions within workspace]
	} catch (error) {
		console.log('Error while reading CFile\n', error);
	}
	// // copy and reverse key-values (for later reference)
	// const pathFunctionMap = Object.fromEntries(
	// 	Object.entries(context.functionMap).map(([key, value]) => [value, key])
	// );
	// let parameters = false;
	// if (function_name.endsWith(')')) {
	// 	// since parameters are specified, it'll have to be an exact match
	// 	parameters = true;
	// }

	// Parse for function name within (case-sensitive, startswith match)
	for (let func in context.functionMap) {
		// because it has to be an exact match, now that all functions are taken into account
		// (parameters) ? funcProcessed = key : funcProcessed = key.match(/^(\w+)/)[1];
		if (func.startsWith(function_name) && cProjectDir === context.functionMap[func]) { // if found return context
			// const output = [
			// 	context.functionMap[key],
			// pathFunctionMap,
			// 	context.functionMap,
			// 	context.adjacencyMatrix,
			// 	context.functionIndex
			// ];
			return [func, context];
		}
	}
	// function not found
	vscode.window.showErrorMessage(`Specified function ${function_name} was not found within active file`);
	return null; // Return null if no match found
}

// function to call for creating hashmap {funcName: code}
function extractCode(entry_point, context) {
	const reverseDict = (obj) => Object.fromEntries(Object.entries(obj).map(([k, v]) => [v, k]));
	const indexFunction = reverseDict(context.functionIndex);
	const all_code = {};
	const visited = new Set(); // track visited functions
	let queue = [entry_point];
	while (queue.length > 0) {
		const func = queue.shift();
		if (!visited.has(func)) {
			// extract code
			all_code[func] = extractFunctionCode(context.functionMap[func], func);
			visited.add(func); // push into set
			const index = context.functionIndex[func];
			const n = context.adjacencyMatrix.length;
			try{
				for (let i = 0; i < n; i++) {
					const value = context.adjacencyMatrix[index][i];
					if (value === 1) {
						const funcChildren = indexFunction[i];
						queue.push(funcChildren) // push into queue for BFS
					}
				}
			} catch (error) {
				console.log(`Function not found in adjacency matrix (extractCode function extension.js): ${error}`);
			}

		}

	}
	return all_code;
}

// function to call Django backend
async function sendRequest(entry_point, context, all_code, tree) {
	const url = "http://localhost:8000/generate"; // Django typically starts at port 8000 local
	const payload = {
		entry: entry_point,
		context: context,
		code: all_code,
		dir_tree: tree
	};
	console.log(payload); // print what we're sending to backend
	try {
		const response = await fetch(url, {
			method: "POST",
			headers: {
				"Content-Type": "application/json"
			},
			body: JSON.stringify(payload)
		});
		const data = await response.json();
		return data;
	} catch (error) {
		console.log("Something went wrong with API call to backend:", error);
	}
	return null;
}

// function to write report and open within user VS code workspace
function writeAndOpenFile(current_path, fileContent) {
	const harnessName = fileContent.harness_name;
	const filePath = path.join(current_path, `${harnessName}_report.txt`);

	const harnessSuccess = fileContent.success;
	const harnessCode = fileContent.harness.split('\n');
	const harnessReport = fileContent.report.split('\n');

	// Write the file
	// Prepare content line by line
	const content = [
		`Harness test successful? ${harnessSuccess ? "True" : "False"}`,
		"Harness:",
		...harnessCode, // Insert harness line by line
		"Report:",
		harnessReport
	].join("\n");
	fs.writeFile(filePath, content, "utf8", (err) => {
		if (err) {
			vscode.window.showErrorMessage("Failed to write report.");
			return;
		}
		// Show a success message
		vscode.window.showInformationMessage(`${harnessName} report completed\n${filePath}`);

		// Open the file inside VS Code
		vscode.workspace.openTextDocument(filePath).then((doc) => {
			vscode.window.showTextDocument(doc);
		});
	});
}



// This method is called when your extension is activated
// Your extension is activated the very first time the command is executed
/**
 * @param {vscode.ExtensionContext} context
 */
function activate(context) {
	// Use the console to output diagnostic information (console.log) and errors (console.error)
	// This line of code will only be executed once when your extension is activated
	console.log('Congratulations, your extension "harness" is now active!');
	// The command has been defined in the package.json file
	// Now provide the implementation of the command with  registerCommand
	// The commandId parameter must match the command field in package.json

	// hello world function (for testing)
	const disposable = vscode.commands.registerCommand('harness.helloworld', function () {
		// The code you place here will be executed every time your command is executed
		// Display a message box to the user
		console.log("Extension Successfully Activated")
		vscode.window.showInformationMessage('Hello World from the harness extension!');
	});
	// generation function
	const generation = vscode.commands.registerCommand('harness.generation', async function () {
		console.log('Harness generation called');
		// Usage
		const folderUri = vscode.workspace.workspaceFolders?.[0]?.uri;
		if (!folderUri) {
			vscode.window.showErrorMessage("No workspace folder is open.");
			return;
		}
		// 
		// Convert that URI to a standard file system path.
		const workspacePath = folderUri.fsPath;
		// traverse that path to get dir tree structure (can be used later in error logging)
		const tree = getDirectoryTree(workspacePath, {
			ignore: ['.git', 'node_modules'],
			maxDepth: 3 // maximum depth is limited to 3 for now
		});
		// console.log(tree);
		const editor = vscode.window.activeTextEditor;
		let filePath;
		let parentDirectory; // this is where the report will be generated
		let file_name;
		if (editor) {
			filePath = editor.document.uri.fsPath; // Get the full path
			parentDirectory = path.dirname(filePath); // Get the parent directory name
			const getFileExtension = path => path.replace(/.*\//, ''); // function to get file name
			file_name = getFileExtension(filePath);
			// console.log(file_name);
			if (!file_name.endsWith('.c')) {
				vscode.window.showErrorMessage("Current active file must be a C file!");
				return;
			}
		} else {
			vscode.window.showErrorMessage("No active file in workspace found!");
			return;
		}
		vscode.window.showInformationMessage(`Harness generation extension activated on ${file_name}`);
		const cProjectDir = filePath; // user specified file and function should be within project directory
		// console.log("Navigating into cProjectDir:", cProjectDir);
		// prompt the user for target function name
		let function_name = await vscode.window.showInputBox({ prompt: 'Enter target function name' });
		if (!function_name) {
			vscode.window.showErrorMessage(`Target function name within ${file_name} is required!`);
			return;
		}
		// if user has included parentheses in any way
		if (function_name.includes('(')) function_name = function_name.slice(0, function_name.indexOf('('));
		// parse specified C file for target function
		const context_output = readCFile(workspacePath, cProjectDir, function_name);
		if (context_output === null) return;
		// Execute logic using the provided inputs
		vscode.window.showInformationMessage(`Generating harness for: ${file_name} -> Function: ${function_name}`);
		const entry_point = context_output[0];
		const context = context_output[1];
		// extract code function (BFS)
		const all_code = extractCode(entry_point, context);
		// all the code {function name: code} (debugging purposes)
		// for (let function_key in all_code) console.log(`Function: ${function_key}, code: ${all_code[function_key]}`);

		const output = await sendRequest(entry_point, context, all_code, tree); // call backend
		console.log(output);
		const status = output["status"]
		const message = output["message"]
		if (status !== 200) {
			vscode.window.showErrorMessage(`Request response ${status} with message ${message}`)
			return;
		}
		writeAndOpenFile(parentDirectory, output); // write and open report within user workspace
	});

	// cleanup
	context.subscriptions.push(disposable);
	context.subscriptions.push(generation);
}

// This method is called when your extension is deactivated
function deactivate() { }

module.exports = {
	activate,
	deactivate
}
