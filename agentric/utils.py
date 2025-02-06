def read_c_file(filepath: str) -> str:
        with open(filepath, 'r') as f:
            return f.read()

def save_c_file(content: str, filename: str) -> str:
    filepath = os.path.join(self.code_dir, filename)
    with open(filepath, 'w') as f:
        f.write(content)
    return filepath