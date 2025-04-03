#!/bin/bash
# Setup script for CBMC Harness Generator

# Exit on any error
set -e

echo "Setting up CBMC Harness Generator..."

# Check if Python 3.9+ is installed (due to langgraph requirements)
if ! command -v python3 &> /dev/null; then
    echo "Error: Python 3 is not installed. Please install Python 3.9 or higher."
    exit 1
fi

PYTHON_VERSION=$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')
if (( $(echo "$PYTHON_VERSION < 3.9" | bc -l) )); then
    echo "Error: Python version must be 3.9 or higher. Found version $PYTHON_VERSION"
    exit 1
fi

echo "Found Python $PYTHON_VERSION"

# Check if CBMC is installed
if ! command -v cbmc &> /dev/null; then
    echo "Warning: CBMC is not installed or not in PATH."
    
    # Suggest installation based on OS
    if [[ "$OSTYPE" == "linux-gnu"* ]]; then
        echo "For Ubuntu/Debian, install CBMC using: sudo apt-get install cbmc"
        echo "Or download from: https://github.com/diffblue/cbmc"
    elif [[ "$OSTYPE" == "darwin"* ]]; then
        echo "For macOS, install CBMC using: brew install cbmc"
        echo "Or download from: https://github.com/diffblue/cbmc/releases"
    elif [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" ]]; then
        echo "For Windows, download CBMC from: https://github.com/diffblue/cbmc/releases"
    fi
    
    read -p "Do you want to continue without CBMC? (y/n) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Setup aborted. Please install CBMC and run setup again."
        exit 1
    fi
else
    CBMC_VERSION=$(cbmc --version | head -n 1)
    echo "Found $CBMC_VERSION"
fi

# Create Python virtual environment
echo "Creating Python virtual environment..."
python3 -m venv venv
source venv/bin/activate

# Upgrade pip and install dependencies
echo "Upgrading pip and installing Python dependencies..."
pip install --upgrade pip
pip install -r requirements.txt

# Create necessary directories for the project
echo "Creating project directories..."
mkdir -p results/harnesses \
          results/verification \
          results/reports \
          results/rag_data

# Set up environment variable for API keys
echo "Setting up API keys for LLMs..."

# Anthropic API key setup
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Anthropic API key is not set."
    read -p "Enter your Anthropic API key (or press Enter to skip): " api_key
    if [ ! -z "$api_key" ]; then
        export ANTHROPIC_API_KEY="$api_key"
        echo "export ANTHROPIC_API_KEY=\"$api_key\"" >> ~/.bashrc
        echo "Added Anthropic API key to ~/.bashrc. Run 'source ~/.bashrc' to apply in current session."
    else
        echo "Skipping Anthropic API key setup. Claude LLM will not be available."
    fi
else
    echo "Anthropic API key is already set."
fi

# OpenAI API key setup
if [ -z "$OPENAI_API_KEY" ]; then
    echo "OpenAI API key is not set."
    read -p "Enter your OpenAI API key (or press Enter to skip): " api_key
    if [ ! -z "$api_key" ]; then
        export OPENAI_API_KEY="$api_key"
        echo "export OPENAI_API_KEY=\"$api_key\"" >> ~/.bashrc
        echo "Added OpenAI API key to ~/.bashrc. Run 'source ~/.bashrc' to apply in current session."
    else
        echo "Skipping OpenAI API key setup. OpenAI LLM will not be available."
    fi
else
    echo "OpenAI API key is already set."
fi

# Google Gemini API key setup
if [ -z "$GOOGLE_API_KEY" ]; then
    echo "Google Gemini API key is not set."
    read -p "Enter your Google Gemini API key (or press Enter to skip): " api_key
    if [ ! -z "$api_key" ]; then
        export GOOGLE_API_KEY="$api_key"
        echo "export GOOGLE_API_KEY=\"$api_key\"" >> ~/.bashrc
        echo "Added Google Gemini API key to ~/.bashrc. Run 'source ~/.bashrc' to apply in current session."
    else
        echo "Skipping Google Gemini API key setup. Gemini LLM will not be available."
    fi
else
    echo "Google Gemini API key is already set."
fi

# Create a startup script to activate virtual environment
echo "#!/bin/bash
source venv/bin/activate
python main.py \"\$@\"" > run.sh
chmod +x run.sh

echo
echo "Setup complete! You can now run the CBMC Harness Generator using these options:"
echo
echo "1. Activate the virtual environment:"
echo "   source venv/bin/activate"
echo
echo "2. Run the generator with various options:"
echo "   # Single file processing (default Claude)"
echo "   python main.py -f path/to/your/file.c"
echo
echo "   # Specify LLM explicitly:"
echo "   python main.py -f path/to/your/file.c --llm claude"
echo "   python main.py -f path/to/your/file.c --llm openai"
echo "   python main.py -f path/to/your/file.c --llm gemini"
echo
echo "   # Directory processing:"
echo "   python main.py -d path/to/your/project"
echo
echo "3. Or use the convenient run script:"
echo "   ./run.sh -f path/to/your/file.c"
echo
echo "Ensure the appropriate API key is set for the LLM you want to use."
echo "Check the documentation at https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering/overview"