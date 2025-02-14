const fs = require('fs');
const path = require('path');

/**
 * Recursively gather all .c and .h files from a given directory.
 * @param {string} dir      The starting directory.
 * @param {Array}  allFiles An accumulating array of file paths.
 * @returns {Array}         The array of discovered file paths (.c or .h).
 */
function getAllCAndHeaderFiles(dir, allFiles = []) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });

  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);

    if (entry.isDirectory()) {
      // Recur into subdirectories
      getAllCAndHeaderFiles(fullPath, allFiles);
    } else if (entry.isFile()) {
      // If it's a .c or .h, store it
      if (/\.(c|h)$/i.test(fullPath)) {
        allFiles.push(fullPath);
      }
    }
  }

  return allFiles;
}

module.exports = {
  getAllCAndHeaderFiles
};
