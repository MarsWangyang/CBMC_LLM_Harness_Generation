#!/bin/bash
# Setup script for CBMC Harness Generator
# Cross-platform compatible for Linux, macOS, and Windows (Git Bash/WSL)

# Exit on any error
set -e

echo "Setting up CBMC Harness Generator..."

# Detect operating system
if [[ "$OSTYPE" == "linux-gnu"* ]]; then
    OS_TYPE="Linux"
    SHELL_RC="$HOME/.bashrc"
    if [ -f /etc/os-release ]; then
        source /etc/os-release
        if [[ "$ID" == "linuxmint" || "$ID_LIKE" == *"ubuntu"* ]]; then
            PACKAGE_MANAGER="apt-get"
        elif [[ "$ID" == "fedora" || "$ID_LIKE" == *"rhel"* ]]; then
            PACKAGE_MANAGER="dnf"
        fi
    fi
elif [[ "$OSTYPE" == "darwin"* ]]; then
    OS_TYPE="macOS"
    # Check for default shell on macOS
    if [[ "$SHELL" == *"zsh"* ]]; then
        SHELL_RC="$HOME/.zshrc"
    else
        SHELL_RC="$HOME/.bash_profile"
    fi
elif [[ "$OSTYPE" == "msys" || "$OSTYPE" == "cygwin" || "$OSTYPE" == "win32" ]]; then
    OS_TYPE="Windows"
    SHELL_RC="$HOME/.bashrc"  # For Git Bash
elif [[ -n "$WSL_DISTRO_NAME" ]]; then
    OS_TYPE="WSL"
    SHELL_RC="$HOME/.bashrc"
else
    OS_TYPE="Unknown"
    SHELL_RC="$HOME/.bashrc"
    echo "Warning: Unrecognized operating system. Using default configuration."
fi

echo "Detected operating system: $OS_TYPE"

# Check if Python 3.9+ is installed (due to langgraph requirements)
if ! command -v python3 &> /dev/null; then
    echo "Error: Python 3 is not installed. Please install Python 3.9 or higher."
    if [[ "$OS_TYPE" == "Linux" && -n "$PACKAGE_MANAGER" ]]; then
        echo "Try: sudo $PACKAGE_MANAGER install python3 python3-pip python3-venv"
    elif [[ "$OS_TYPE" == "macOS" ]]; then
        echo "Try: brew install python3"
    elif [[ "$OS_TYPE" == "Windows" || "$OS_TYPE" == "WSL" ]]; then
        echo "Download Python from https://www.python.org/downloads/"
    fi
    exit 1
fi

# Check Python version - compatible across platforms
PYTHON_VERSION=$(python3 -c 'import sys; print(f"{sys.version_info.major}.{sys.version_info.minor}")')
MAJOR_VERSION=$(echo $PYTHON_VERSION | cut -d. -f1)
MINOR_VERSION=$(echo $PYTHON_VERSION | cut -d. -f2)

if [[ "$MAJOR_VERSION" -lt 3 || ("$MAJOR_VERSION" -eq 3 && "$MINOR_VERSION" -lt 9) ]]; then
    echo "Error: Python version must be 3.9 or higher. Found version $PYTHON_VERSION"
    exit 1
fi

echo "Found Python $PYTHON_VERSION"

# Check if CBMC is installed
if ! command -v cbmc &> /dev/null; then
    echo "Warning: CBMC is not installed or not in PATH."
    
    # Suggest installation based on OS
    if [[ "$OS_TYPE" == "Linux" ]]; then
        if [[ "$PACKAGE_MANAGER" == "apt-get" ]]; then
            echo "For Ubuntu/Debian/Linux Mint, install CBMC using: sudo apt-get install cbmc"
        elif [[ "$PACKAGE_MANAGER" == "dnf" ]]; then
            echo "For Fedora/RHEL, install CBMC using: sudo dnf install cbmc"
        fi
        echo "Or download from: https://github.com/diffblue/cbmc"
    elif [[ "$OS_TYPE" == "macOS" ]]; then
        echo "For macOS, install CBMC using: brew install cbmc"
        echo "Or download from: https://github.com/diffblue/cbmc/releases"
    elif [[ "$OS_TYPE" == "Windows" || "$OS_TYPE" == "WSL" ]]; then
        echo "For Windows, download CBMC from: https://github.com/diffblue/cbmc/releases"
        echo "For WSL, use the appropriate Linux instructions"
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


# Create Python virtual environment - cross-platform
echo "Creating Python virtual environment..."
python3 -m venv venv

# Activate virtual environment (shell-specific)
if [[ "$OS_TYPE" == "Windows" && ! "$OSTYPE" == "cygwin" && ! -n "$WSL_DISTRO_NAME" ]]; then
    echo "Activating virtual environment (Windows)..."
    # For Windows cmd.exe - create a separate cmd file
    echo "@echo off
call venv\Scripts\activate.bat
pip install --upgrade pip
pip install -r requirements.txt" > setup_win.cmd
    
    echo "Please run setup_win.cmd to complete installation"
    
    # For PowerShell users
    echo "# PowerShell users run:
# venv\Scripts\Activate.ps1" > setup_win.ps1
    
    # Continue with directory creation
else
    # Unix-like systems (Linux, macOS, Git Bash, WSL)
    echo "Activating virtual environment (Unix-like)..."
    if [[ "$OS_TYPE" == "Windows" && "$OSTYPE" == "msys" ]]; then
        # Git Bash on Windows needs special handling
        source venv/Scripts/activate
    else
        source venv/bin/activate
    fi
    
    # Upgrade pip and install dependencies
    echo "Upgrading pip and installing Python dependencies..."
    pip install --upgrade pip
    pip install -r requirements.txt
fi

# Create necessary directories for the project
echo "Creating project directories..."
mkdir -p results/harnesses \
          results/verification \
          results/reports \
          results/rag_data

# Set up environment variable for API keys
echo "Setting up API keys for LLMs..."

# Function to safely add environment variables
add_env_var() {
    local key=$1
    local value=$2
    local rcfile=$3
    
    # Don't add if empty
    if [ -z "$value" ]; then
        return
    fi
    
    # Export for current session
    export "$key=$value"
    
    # Check if already in RC file to avoid duplicates
    if ! grep -q "export $key=" "$rcfile" 2>/dev/null; then
        echo "export $key=\"$value\"" >> "$rcfile"
        echo "Added $key to $rcfile"
    else
        echo "$key is already in $rcfile"
    fi
}

# Anthropic API key setup
if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Anthropic API key is not set."
    read -p "Enter your Anthropic API key (or press Enter to skip): " api_key
    if [ ! -z "$api_key" ]; then
        add_env_var "ANTHROPIC_API_KEY" "$api_key" "$SHELL_RC"
        echo "Run 'source $SHELL_RC' to apply in current session."
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
        add_env_var "OPENAI_API_KEY" "$api_key" "$SHELL_RC"
        echo "Run 'source $SHELL_RC' to apply in current session."
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
        add_env_var "GOOGLE_API_KEY" "$api_key" "$SHELL_RC"
        echo "Run 'source $SHELL_RC' to apply in current session."
    else
        echo "Skipping Google Gemini API key setup. Gemini LLM will not be available."
    fi
else
    echo "Google Gemini API key is already set."
fi

# Create platform-specific startup scripts
if [[ "$OS_TYPE" == "Windows" && ! "$OSTYPE" == "cygwin" && ! -n "$WSL_DISTRO_NAME" ]]; then
    # Windows batch file
    echo "@echo off
call venv\Scripts\activate.bat
python main.py %*" > run.bat
    chmod +x run.bat
    
    # Windows PowerShell script
    echo "# PowerShell script to run the generator
.\venv\Scripts\Activate.ps1
python main.py `$args" > run.ps1
else
    # Unix-like script (Linux, macOS, Git Bash, WSL)
    if [[ "$OS_TYPE" == "Windows" && "$OSTYPE" == "msys" ]]; then
        # Git Bash on Windows
        echo "#!/bin/bash
source venv/Scripts/activate
python main.py \"\$@\"" > run.sh
    else
        # Standard Unix
        echo "#!/bin/bash
source venv/bin/activate
python main.py \"\$@\"" > run.sh
    fi
    chmod +x run.sh
fi

echo
echo "Setup complete! You can now run the CBMC Harness Generator using these options:"
echo

if [[ "$OS_TYPE" == "Windows" && ! "$OSTYPE" == "cygwin" && ! -n "$WSL_DISTRO_NAME" ]]; then
    echo "For Windows users:"
    echo "1. Run the generator with the batch file:"
    echo "   run.bat -f path/to/your/file.c"
    echo
    echo "2. Or with PowerShell:"
    echo "   .\run.ps1 -f path/to/your/file.c"
else
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
fi

echo
echo "Ensure the appropriate API key is set for the LLM you want to use."
echo "Check the documentation at https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering/overview"