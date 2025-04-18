# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 143.30 seconds
Processed 3 source files.
Analyzed 10 functions.
Identified 8 functions with memory or arithmetic operations.
Generated 8 verification harnesses.
Performed 27 harness refinements (average 3.38 per function).

## File Analysis

### defender.c
Functions analyzed: 8
Functions verified: 8
Successful verifications: 6
Failed verifications: 2

## RAG Knowledge Base Statistics
Code functions stored: 15
Pattern templates: 16
Error patterns stored: 21
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 8
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 8
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 0 of 8
Functions without errors: 8 of 8

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Coverage Matrix by Function and Version

The table below shows the coverage metrics for each function across different versions of the generated harnesses:

| Function | Version 1 ||| Version 2 ||| Version 3 ||| Version 4 ||| Version 5 ||| Version 6 ||| Version 7 ||| Version 8 ||| Version 9 ||
| --- | Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func |
| defender.c:Defender_GetTopic | 94.44% | 91.30% || 94.87% | 91.30% || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:Defender_MatchTopic | 75.86% | 70.21% || 76.27% | 70.21% || 76.27% | 70.21% || 76.27% | 70.21% || 75.44% | 70.21% || 76.27% | 70.21% || 76.27% | 70.21% || 77.78% | 70.21% || 77.78% | 70.21% |
| defender.c:extractThingNameLength | 100.00% | 100.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| defender.c:getTopicLength | 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:matchApi | 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:matchBridge | 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:matchPrefix | 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:writeFormatAndSuffix | 0.00% | 0.00% || 100.00% | 100.00% || 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - |

**Note:** 'Total' shows the percentage of all reachable lines that were covered during verification. 'Func' shows the percentage of target function lines that were covered.

## Performance Metrics
Average harness generation time: 5.08 seconds
Average verification time: 0.42 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html
Detailed metrics available in: coverage/coverage_metrics.csv

## Summary of Results

### Function: Defender_GetTopic (File: defender.c)
Status: SUCCESS
Refinements: 2
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:Defender_GetTopic/v1.c
  - Version 2: results/openai/20250417_232117/harnesses/defender.c:Defender_GetTopic/v2.c
  - Size evolution: Initial 41 lines → Final 47 lines (+6 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v2_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v3_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_GetTopic/v3_report.md

### Function: Defender_MatchTopic (File: defender.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Null pointer dereference detected
Suggestions: Add null pointer checks before dereferencing pointers

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v1.c
  - Version 2: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v2.c
  - Version 3: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v3.c
  - Version 4: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v4.c
  - Version 5: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v5.c
  - Version 6: results/openai/20250417_232117/harnesses/defender.c:Defender_MatchTopic/v6.c
  - Size evolution: Initial 32 lines → Final 39 lines (+7 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v2_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v3_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v3_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v4_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v4_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v5_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v5_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v6_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v6_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v7_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v7_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v8_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v8_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v9_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v9_report.md
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v10_results.txt
  - results/openai/20250417_232117/verification/defender.c:Defender_MatchTopic/v10_report.md

### Function: extractThingNameLength (File: defender.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Unspecified verification error
Suggestions: Review the full verification output for details

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v1.c
  - Version 2: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v2.c
  - Version 3: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v3.c
  - Version 4: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v4.c
  - Version 5: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v5.c
  - Version 6: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v6.c
  - Version 7: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v7.c
  - Version 8: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v8.c
  - Version 9: results/openai/20250417_232117/harnesses/defender.c:extractThingNameLength/v9.c
  - Size evolution: Initial 29 lines → Final 124 lines (+95 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v2_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v3_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v3_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v4_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v4_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v5_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v5_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v6_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v6_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v7_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v7_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v8_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v8_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v9_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v9_report.md
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v10_results.txt
  - results/openai/20250417_232117/verification/defender.c:extractThingNameLength/v10_report.md

### Function: getTopicLength (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:getTopicLength/v1.c

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:getTopicLength/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:getTopicLength/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:getTopicLength/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:getTopicLength/v2_report.md

### Function: matchApi (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:matchApi/v1.c

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:matchApi/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchApi/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:matchApi/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchApi/v2_report.md

### Function: matchBridge (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:matchBridge/v1.c

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:matchBridge/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchBridge/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:matchBridge/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchBridge/v2_report.md

### Function: matchPrefix (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:matchPrefix/v1.c

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:matchPrefix/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchPrefix/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:matchPrefix/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:matchPrefix/v2_report.md

### Function: writeFormatAndSuffix (File: defender.c)
Status: SUCCESS
Refinements: 3
Message: Verification successful

#### Coverage Metrics
- Total reachable lines: 1
- Total coverage: 0.00%
- Function reachable lines: 1
- Function coverage: 0.00%
- Reported errors: 0

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v9): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250417_232117/harnesses/defender.c:writeFormatAndSuffix/v1.c
  - Version 2: results/openai/20250417_232117/harnesses/defender.c:writeFormatAndSuffix/v2.c
  - Version 3: results/openai/20250417_232117/harnesses/defender.c:writeFormatAndSuffix/v3.c
  - Size evolution: Initial 43 lines → Final 48 lines (+5 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v1_results.txt
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v1_report.md
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v2_results.txt
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v2_report.md
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v3_results.txt
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v3_report.md
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v4_results.txt
  - results/openai/20250417_232117/verification/defender.c:writeFormatAndSuffix/v4_report.md