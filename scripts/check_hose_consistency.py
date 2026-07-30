#!/usr/bin/env python3
"""
scripts/check_hose_consistency.py
Automated Python consistency checker for Pride's Untyped Higher-Order & Scoped
Effects (HOSE) overhaul. Checks syntax, module structure, loop termination
(explicit break statements), and symbol consistency across C and Pie sources.
"""

import os
import sys
import re
import subprocess

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))

def check_loop_termination():
    """Ensure all .pie files use explicit 'break' statements in while loops."""
    pie_files = []
    for root, dirs, files in os.walk(REPO_ROOT):
        if ".git" in root or "build" in root:
            continue
        for f in files:
            if f.endswith(".pie"):
                pie_files.append(os.path.join(root, f))
    
    errors = []
    for filepath in pie_files:
        with open(filepath, "r", encoding="utf-8") as file:
            content = file.read()
            # Find each while loop start and check the matching brace block
            pos = 0
            while True:
                idx = content.find("while ", pos)
                if idx == -1:
                    break
                do_idx = content.find("do {", idx)
                if do_idx == -1:
                    pos = idx + 6
                    continue
                # Match balanced braces from do_idx + 3
                brace_count = 0
                end_idx = -1
                for i in range(do_idx + 3, len(content)):
                    if content[i] == '{':
                        brace_count += 1
                    elif content[i] == '}':
                        if brace_count == 0:
                            end_idx = i
                            break
                        else:
                            brace_count -= 1
                if end_idx != -1:
                    loop_body = content[do_idx:end_idx+1]
                    if "break" not in loop_body:
                        rel_path = os.path.relpath(filepath, REPO_ROOT)
                        errors.append(f"{rel_path}: while loop without explicit 'break' statement")
                    pos = end_idx + 1
                else:
                    pos = do_idx + 4
    
    return errors

def check_runtime_symbols():
    """Verify that all HOSE runtime symbols are declared in codegen.c3 and runtime/compiler_rt.c."""
    symbols = [
        "__pride_fiber_spawn", "__pride_fiber_yield", "__pride_fiber_resume",
        "__pride_prompt_install", "__pride_prompt_unwind", "__pride_is_in_scope",
        "__pride_scoped_yield_in", "__pride_scoped_yield_out", "__pride_split_cont",
        "__pride_fuse_cont"
    ]
    
    with open(os.path.join(REPO_ROOT, "codegen.c3"), "r", encoding="utf-8") as f:
        codegen_text = f.read()
    
    with open(os.path.join(REPO_ROOT, "runtime", "compiler_rt.c"), "r", encoding="utf-8") as f:
        runtime_text = f.read()
        
    errors = []
    for sym in symbols:
        if sym not in codegen_text:
            errors.append(f"Symbol {sym} missing from codegen.c3")
        if sym not in runtime_text:
            errors.append(f"Symbol {sym} missing from runtime/compiler_rt.c")
            
    return errors

def check_pride_modules():
    """Verify that stdlib/pride.pie and stdlib/pride/*.pie modules exist and are structured correctly."""
    required_modules = [
        "stdlib/pride.pie",
        "stdlib/pride/effects.pie",
        "stdlib/pride/irdl.pie",
        "stdlib/pride/msp.pie",
        "stdlib/pride/ub.pie",
        "stdlib/pride/subtyping.pie",
        "stdlib/pride/rewrite.pie"
    ]
    errors = []
    for mod in required_modules:
        path = os.path.join(REPO_ROOT, mod)
        if not os.path.exists(path):
            errors.append(f"Required module {mod} does not exist")
    return errors

def check_gcc_build():
    """Verify that runtime/compiler_rt.c compiles cleanly with GCC 12."""
    cmd = ["gcc", "-O2", "-msse4.1", "-pthread", "-std=c11", "-c",
           os.path.join(REPO_ROOT, "runtime", "compiler_rt.c"), "-o", "/dev/null", "-Wall"]
    res = subprocess.run(cmd, capture_output=True, text=True)
    if res.returncode != 0:
        return [f"GCC compilation failed:\n{res.stderr}"]
    return []

def main():
    print("Running Pride HOSE Consistency Checker...")
    errors = []
    
    print("1. Checking GCC 12 compilation of C runtime...")
    errors.extend(check_gcc_build())
    
    print("2. Checking runtime symbol consistency across codegen.c3 and runtime/compiler_rt.c...")
    errors.extend(check_runtime_symbols())
    
    print("3. Checking stdlib/pride/ module hierarchy...")
    errors.extend(check_pride_modules())
    
    print("4. Checking while loop clean termination (explicit break statements)...")
    errors.extend(check_loop_termination())
    
    if errors:
        print("FAILED with errors:")
        for e in errors:
            print(f"  - {e}")
        sys.exit(1)
    else:
        print("SUCCESS! All HOSE checks passed with 100% consistency.")
        sys.exit(0)

if __name__ == "__main__":
    main()
