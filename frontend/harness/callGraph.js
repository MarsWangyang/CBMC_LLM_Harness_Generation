const path = require('path');
const { getAllCAndHeaderFiles } = require('./getAllCAndHeaderFiles');
const { collectLocalFunctions, extractFunctionsAndCalls, buildAdjacencyMatrix } = require('./parserCore');

function parseProject(projectPath) {
    const allFiles = getAllCAndHeaderFiles(projectPath);

    let functionMap = {};
    let callMatrix = {};
    let allFunctions = [];

    // FIRST PASS: populate functionMap from definitions
    allFiles.forEach(filePath => {
        collectLocalFunctions(filePath, functionMap);
    });

    // SECOND PASS: gather calls, but skip calls to functions not in functionMap
    allFiles.forEach(filePath => {
        extractFunctionsAndCalls(filePath, functionMap, callMatrix, allFunctions);
    });
    // console.log("Function Map:", functionMap);
    // console.log("All functions:", allFunctions);
    const { matrix, functionIndex } = buildAdjacencyMatrix(allFunctions, callMatrix);
    return {
        functionMap,
        callMatrix,
        adjacencyMatrix: matrix,
        functionIndex,
        allFunctions
    };
}


// To test directly from CLI (example: node parseProject.js my_project)
if (require.main === module) {
    if (process.argv.length < 3) {
        console.error("Usage: node parseProject.js <path-to-project>");
        process.exit(1);
    }

    const projectPath = path.resolve(process.argv[2]);
    const result = parseProject(projectPath);

    // Print out the JSON structure
    console.log(JSON.stringify(result, null, 2));
}

module.exports = {
    parseProject
};
