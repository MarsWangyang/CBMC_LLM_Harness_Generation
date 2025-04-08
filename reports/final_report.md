# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 1260.17 seconds
Processed 5 source files.
Analyzed 85 functions.
Identified 36 functions with memory or arithmetic operations.
Generated 36 verification harnesses.
Performed 27 harness refinements (average 0.75 per function).

## File Analysis

### core_json.c
Functions analyzed: 32
Functions verified: 32
Successful verifications: 29
Failed verifications: 3

### pattern
Functions analyzed: 4
Functions verified: 4
Successful verifications: 4
Failed verifications: 0

## RAG Knowledge Base Statistics
Code functions stored: 93
Pattern templates: 16
Error patterns stored: 0
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 0
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 0
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 0 of 36
Functions without errors: 36 of 36

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Performance Metrics
Average harness generation time: 3.73 seconds
Average verification time: 4.42 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html
Detailed metrics available in: coverage/coverage_metrics.csv

## Summary of Results

### Function: JSON_Iterate (File: core_json.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Null pointer dereference detected
Suggestions: Add null pointer checks before dereferencing pointers

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v1.c
  - Version 2: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v2.c
  - Version 3: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v3.c
  - Version 4: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v4.c
  - Version 5: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v5.c
  - Version 6: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v6.c
  - Version 7: results/openai/20250407_133402/harnesses/core_json.c:JSON_Iterate/v7.c
  - Size evolution: Initial 40 lines → Final 55 lines (+15 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v1_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v2_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v2_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v3_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v3_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v4_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v4_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v5_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v5_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v6_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v6_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v7_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v7_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v8_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v8_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v9_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v9_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v10_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Iterate/v10_report.md

### Function: JSON_SearchConst (File: core_json.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Null pointer dereference detected
Suggestions: Add null pointer checks before dereferencing pointers

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchConst/v1.c
  - Version 2: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchConst/v2.c
  - Version 3: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchConst/v3.c
  - Version 4: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchConst/v4.c
  - Size evolution: Initial 45 lines → Final 57 lines (+12 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v1_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v2_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v2_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v3_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v3_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v4_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v4_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v5_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v5_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v6_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v6_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v7_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v7_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v8_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v8_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v9_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v9_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v10_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchConst/v10_report.md

### Function: JSON_SearchT (File: core_json.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Unspecified verification error
Suggestions: Review the full verification output for details

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchT/v1.c
  - Version 2: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchT/v2.c
  - Version 3: results/openai/20250407_133402/harnesses/core_json.c:JSON_SearchT/v3.c
  - Size evolution: Initial 43 lines → Final 57 lines (+14 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v1_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v2_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v2_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v3_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v3_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v4_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v4_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v5_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v5_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v6_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v6_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v7_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v7_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v8_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v8_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v9_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v9_report.md
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v10_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_SearchT/v10_report.md

### Function: JSON_Validate (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:JSON_Validate/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:JSON_Validate/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:JSON_Validate/v1_report.md

### Function: arraySearch (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:arraySearch/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:arraySearch/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:arraySearch/v1_report.md

### Function: countHighBits (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:countHighBits/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:countHighBits/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:countHighBits/v1_report.md

### Function: hexToInt (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:hexToInt/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:hexToInt/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:hexToInt/v1_report.md

### Function: multiSearch (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:multiSearch/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:multiSearch/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:multiSearch/v1_report.md

### Function: nextKeyValuePair (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:nextKeyValuePair/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:nextKeyValuePair/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:nextKeyValuePair/v1_report.md

### Function: nextValue (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:nextValue/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:nextValue/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:nextValue/v1_report.md

### Function: shortestUTF8 (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:shortestUTF8/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:shortestUTF8/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:shortestUTF8/v1_report.md

### Function: skipAnyLiteral (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipAnyLiteral/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipAnyLiteral/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipAnyLiteral/v1_report.md

### Function: skipAnyScalar (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipAnyScalar/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipAnyScalar/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipAnyScalar/v1_report.md

### Function: skipArrayScalars (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipArrayScalars/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipArrayScalars/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipArrayScalars/v1_report.md

### Function: skipCollection (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipCollection/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipCollection/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipCollection/v1_report.md

### Function: skipDecimals (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipDecimals/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipDecimals/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipDecimals/v1_report.md

### Function: skipDigits (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipDigits/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipDigits/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipDigits/v1_report.md

### Function: skipEscape (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipEscape/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipEscape/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipEscape/v1_report.md

### Function: skipExponent (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipExponent/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipExponent/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipExponent/v1_report.md

### Function: skipHexEscape (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipHexEscape/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipHexEscape/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipHexEscape/v1_report.md

### Function: skipLiteral (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipLiteral/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipLiteral/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipLiteral/v1_report.md

### Function: skipNumber (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipNumber/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipNumber/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipNumber/v1_report.md

### Function: skipObjectScalars (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipObjectScalars/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipObjectScalars/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipObjectScalars/v1_report.md

### Function: skipOneHexEscape (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipOneHexEscape/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipOneHexEscape/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipOneHexEscape/v1_report.md

### Function: skipQueryPart (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipQueryPart/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipQueryPart/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipQueryPart/v1_report.md

### Function: skipScalars (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipScalars/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipScalars/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipScalars/v1_report.md

### Function: skipSpace (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipSpace/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipSpace/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipSpace/v1_report.md

### Function: skipSpaceAndComma (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipSpaceAndComma/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipSpaceAndComma/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipSpaceAndComma/v1_report.md

### Function: skipString (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipString/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipString/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipString/v1_report.md

### Function: skipUTF8 (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipUTF8/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipUTF8/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipUTF8/v1_report.md

### Function: skipUTF8MultiByte (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:skipUTF8MultiByte/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:skipUTF8MultiByte/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:skipUTF8MultiByte/v1_report.md

### Function: strnEq (File: core_json.c)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/core_json.c:strnEq/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/core_json.c:strnEq/v1_results.txt
  - results/openai/20250407_133402/verification/core_json.c:strnEq/v1_report.md

### Function: core_json.c:for (File: pattern)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/pattern:core_json.c:for/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/pattern:core_json.c:for/v1_results.txt
  - results/openai/20250407_133402/verification/pattern:core_json.c:for/v1_report.md

### Function: core_json.c:if (File: pattern)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/pattern:core_json.c:if/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/pattern:core_json.c:if/v1_results.txt
  - results/openai/20250407_133402/verification/pattern:core_json.c:if/v1_report.md

### Function: core_json.c:switch (File: pattern)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/pattern:core_json.c:switch/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/pattern:core_json.c:switch/v1_results.txt
  - results/openai/20250407_133402/verification/pattern:core_json.c:switch/v1_report.md

### Function: core_json.c:while (File: pattern)
Status: SUCCESS
Refinements: 0
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 0
- Total coverage: 0.00%
- Function reachable lines: 0
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250407_133402/harnesses/pattern:core_json.c:while/v1.c

#### Verification Reports: 
  - results/openai/20250407_133402/verification/pattern:core_json.c:while/v1_results.txt
  - results/openai/20250407_133402/verification/pattern:core_json.c:while/v1_report.md