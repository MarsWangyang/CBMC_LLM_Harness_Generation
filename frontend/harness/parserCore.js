const fs = require('fs');
const Parser = require('tree-sitter');
const C = require('tree-sitter-c');

// Initialize tree-sitter-c parser
const parser = new Parser();
// @ts-ignore
parser.setLanguage(C);

/**
 * Recursively traverse the AST to extract:
 *  - Function definitions (function_definition nodes)
 *  - Function calls (call_expression nodes)
 *
 * @param {string} filePath        Path to the current file being parsed
 * @param {object} functionMap     A map of functionName -> fileWhereDefined
 * @param {object} callMatrix      A map of caller -> { callee: 1, ... }
 * @param {Array}  allFunctions    A de-duplicated array of all function names found
 */
function extractFunctionsAndCalls(filePath, functionMap, callMatrix, allFunctions) {
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    function addFunctionToList(funcName) {
        if (!allFunctions.includes(funcName)) {
            allFunctions.push(funcName);
        }
    }

    function traverse(node, currentFunction = null) {
        if (node.type === 'function_definition') {
            let fullName = null;
            for (let i = 0; i < node.childCount; i++) {
                // we have to account for pointer declarator functions here
                if (node.child(i).type === "function_declarator" || node.child(i).type === "pointer_declarator") {
                    fullName = node.child(i).text.trim();
                    if (fullName[0] === '*') fullName = fullName.slice(0, fullName.indexOf('*'));
                    break;
                }
            }
            if (fullName === null) {
                for (let j = 0; j < node.childCount; j++) {
                    console.log(`Type: ${node.child(j).type}, Text: ${node.child(j).text}`);
                }
                throw new Error(`Parsing functions through AST went wrong in parserCore extractFunctionsAndCalls (check above to debug)`);
            }
            const strippedString = fullName.replace(/\s+/g, '');
            const end = strippedString.indexOf('(');
            const funcName = strippedString.slice(0, end);

            functionMap[funcName] = filePath;
            addFunctionToList(funcName);

            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), funcName);
            }
        } else if (node.type === 'call_expression' && currentFunction) {
            const calledFuncName = node.child(0).text.replace(/\s+/g, '');
            // const calledFuncName = node.child(0).text;
            // Only record if it's in functionMap (i.e., locally defined)
            if (functionMap[calledFuncName]) {
                addFunctionToList(calledFuncName);
                if (!callMatrix[currentFunction]) {
                    callMatrix[currentFunction] = {};
                }
                callMatrix[currentFunction][calledFuncName] = 1;
            }

            // Recurse to catch nested
            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), currentFunction);
            }
        } else {
            for (let i = 0; i < node.childCount; i++) {
                traverse(node.child(i), currentFunction);
            }
        }
    }
    traverse(root);
}


/**
 * Build an adjacency matrix from the aggregated callMatrix and allFunctions array.
 * @param {Array}  allFunctions   A de-duplicated array of all function names
 * @param {object} callMatrix     A map of caller -> { callee: 1, ... }
 * @returns {{ matrix: number[][], functionIndex: object }}
 */
function buildAdjacencyMatrix(allFunctions, callMatrix) {
    // Create a square matrix of 0s
    let matrix = Array.from({ length: allFunctions.length }, () =>
        Array(allFunctions.length).fill(0)
    );

    // Map each function name to its index in allFunctions
    let functionIndex = {};
    allFunctions.forEach((func, idx) => {
        functionIndex[func] = idx;
    });

    // Fill the matrix
    for (let caller in callMatrix) {
        for (let callee in callMatrix[caller]) {
            let i = functionIndex[caller];
            let j = functionIndex[callee];
            matrix[i][j] = 1; // Mark adjacency
        }
    }
    //   console.log('ADJ:', matrix);
    return { matrix, functionIndex };
}

/**
 * Parse the file at `filePath`, look for a `function_definition` AST node
 * whose identifier matches `functionName`, and return its complete source code.
 *
 * @param {string} filePath      The .c file you want to parse.
 * @param {string} functionName  The function name to look for (e.g. "main", "functionA").
 * @returns {string|null}        The entire text of that function definition, or null if not found.
 */
function extractFunctionCode(filePath, functionName) {
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    function findFunctionNode(node) {
        if (node.type === 'function_definition') {
            let declNode = null;

            // Look for the function declarator
            for (let i = 0; i < node.childCount; i++) {
                if (node.child(i).type === "function_declarator" || node.child(i).type === "pointer_declarator") {
                    declNode = node.child(i).text.replace(/\s+/g, '');
                    break;
                }
            }

            if (!declNode) return null;

            // Extract function name (before '(')
            const funcName = declNode.replace(/\(.*/, '');
            if (funcName === functionName) {
                return node; // Found the function definition
            }
        }

        // Recursively search in children
        for (let i = 0; i < node.childCount; i++) {
            const found = findFunctionNode(node.child(i));
            if (found) return found;
        }

        return null;
    }

    const funcNode = findFunctionNode(root);
    return funcNode ? funcNode.text : null;
}


// helper function to only include local functions
function collectLocalFunctions(filePath, functionMap) {
    const sourceCode = fs.readFileSync(filePath, 'utf8');
    const tree = parser.parse(sourceCode);
    const root = tree.rootNode;

    function traverse(node) {
        if (node.type === 'function_definition') {
            let fullName = null;
            for (let i = 0; i < node.childCount; i++) {
                if (node.child(i).type === "function_declarator" || node.child(i).type === "pointer_declarator") {
                    fullName = node.child(i).text.trim();
                    if (fullName[0] === '*') fullName = fullName.slice(0, fullName.indexOf('*'));
                    break;
                }
            }
            if (fullName === null) {
                for (let j = 0; j < node.childCount; j++) {
                    console.log(`Type: ${node.child(j).type}, Text: ${node.child(j).text}`);
                }
                throw new Error(`Parsing functions through AST went wrong in parserCore (check above to debug)`);
            }
            const strippedString = fullName.replace(/\s+/g, '');
            const end = strippedString.indexOf('(');
            const funcName = strippedString.slice(0, end);
            // const funcName = strippedString.replace(/\(.*/, ''); // old code removing parenthese using regex
            functionMap[funcName] = filePath;
        }
        for (let i = 0; i < node.childCount; i++) {
            traverse(node.child(i));
        }
    }

    traverse(root);
}


module.exports = {
    collectLocalFunctions,
    extractFunctionsAndCalls,
    buildAdjacencyMatrix,
    extractFunctionCode
};
