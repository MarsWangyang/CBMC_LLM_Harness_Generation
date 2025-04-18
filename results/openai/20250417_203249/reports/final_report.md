# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 452.71 seconds
Processed 3 source files.
Analyzed 10 functions.
Identified 11 functions with memory or arithmetic operations.
Generated 11 verification harnesses.
Performed 75 harness refinements (average 6.82 per function).

## File Analysis

### defender.c
Functions analyzed: 8
Functions verified: 8
Successful verifications: 2
Failed verifications: 6

### pattern
Functions analyzed: 3
Functions verified: 3
Successful verifications: 1
Failed verifications: 2

## RAG Knowledge Base Statistics
Code functions stored: 15
Pattern templates: 16
Error patterns stored: 72
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 11
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 11
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 0 of 11
Functions without errors: 11 of 11

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Coverage Matrix by Function and Version

The table below shows the coverage metrics for each function across different versions of the generated harnesses:

| Function | Version 1 ||| Version 2 ||| Version 3 ||| Version 4 ||| Version 5 ||| Version 6 ||| Version 7 ||| Version 8 ||| Version 9 ||
| --- | Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func |
| defender.c:Defender_GetTopic | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| defender.c:Defender_MatchTopic | 75.00% | 70.21% || 77.05% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% || 78.46% | 70.21% |
| defender.c:extractThingNameLength | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| defender.c:getTopicLength | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| defender.c:matchApi | 52.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:matchBridge | 52.63% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| defender.c:matchPrefix | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| defender.c:writeFormatAndSuffix | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| pattern:defender.c:for | 100.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| pattern:defender.c:if | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| pattern:defender.c:switch | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |

**Note:** 'Total' shows the percentage of all reachable lines that were covered during verification. 'Func' shows the percentage of target function lines that were covered.

## Performance Metrics
Average harness generation time: 5.55 seconds
Average verification time: 0.26 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html
Detailed metrics available in: coverage/coverage_metrics.csv

## Summary of Results

### Function: Defender_GetTopic (File: defender.c)
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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:Defender_GetTopic/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:Defender_GetTopic/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:Defender_GetTopic/v3.c
  - Size evolution: Initial 57 lines → Final 70 lines (+13 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_GetTopic/v10_report.md

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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:Defender_MatchTopic/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:Defender_MatchTopic/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:Defender_MatchTopic/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/defender.c:Defender_MatchTopic/v4.c
  - Size evolution: Initial 39 lines → Final 55 lines (+16 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:Defender_MatchTopic/v10_report.md

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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:extractThingNameLength/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:extractThingNameLength/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:extractThingNameLength/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/defender.c:extractThingNameLength/v4.c
  - Version 5: results/openai/20250417_203249/harnesses/defender.c:extractThingNameLength/v5.c
  - Size evolution: Initial 37 lines → Final 55 lines (+18 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:extractThingNameLength/v10_report.md

### Function: getTopicLength (File: defender.c)
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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:getTopicLength/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:getTopicLength/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:getTopicLength/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/defender.c:getTopicLength/v4.c
  - Version 5: results/openai/20250417_203249/harnesses/defender.c:getTopicLength/v5.c
  - Size evolution: Initial 38 lines → Final 96 lines (+58 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:getTopicLength/v10_report.md

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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:matchApi/v1.c

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:matchApi/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchApi/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:matchApi/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchApi/v2_report.md

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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:matchBridge/v1.c

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:matchBridge/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchBridge/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:matchBridge/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchBridge/v2_report.md

### Function: matchPrefix (File: defender.c)
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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:matchPrefix/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:matchPrefix/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:matchPrefix/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/defender.c:matchPrefix/v4.c
  - Size evolution: Initial 45 lines → Final 63 lines (+18 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:matchPrefix/v10_report.md

### Function: writeFormatAndSuffix (File: defender.c)
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
  - Version 1: results/openai/20250417_203249/harnesses/defender.c:writeFormatAndSuffix/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/defender.c:writeFormatAndSuffix/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/defender.c:writeFormatAndSuffix/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/defender.c:writeFormatAndSuffix/v4.c
  - Size evolution: Initial 39 lines → Final 63 lines (+24 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v1_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v1_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v2_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v2_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v3_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v3_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v4_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v4_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v5_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v5_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v6_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v6_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v7_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v7_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v8_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v8_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v9_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v9_report.md
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v10_results.txt
  - results/openai/20250417_203249/verification/defender.c:writeFormatAndSuffix/v10_report.md

### Function: defender.c:for (File: pattern)
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
  - Version 1: results/openai/20250417_203249/harnesses/pattern:defender.c:for/v1.c

#### Verification Reports: 
  - results/openai/20250417_203249/verification/pattern:defender.c:for/v1_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:for/v1_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:for/v2_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:for/v2_report.md

### Function: defender.c:if (File: pattern)
Status: FAILED
Refinements: 9
Message: PREPROCESSING ERROR: Macro definition error: file results/openai/20250417_203249/verification/includes/defender_config.h line 52: results/openai/20250417_203249/verification/includes/defender_config.h:52:13: warning: 'LogError' macro redefined [-Wmacro-redefined]; file results/openai/20250417_203249/verification/includes/defender_config.h line 54: results/openai/20250417_203249/verification/includes/defender_config.h:54:13: warning: 'LogWarn' macro redefined [-Wmacro-redefined]
Suggestions: Fix macro definitions and ensure they are properly defined

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
  - Version 1: results/openai/20250417_203249/harnesses/pattern:defender.c:if/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/pattern:defender.c:if/v2.c
  - Size evolution: Initial 36 lines → Final 46 lines (+10 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v1_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v1_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v2_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v2_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v3_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v3_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v4_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v4_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v5_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v5_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v6_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v6_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v7_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v7_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v8_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v8_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v9_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v9_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v10_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:if/v10_report.md

### Function: defender.c:switch (File: pattern)
Status: FAILED
Refinements: 9
Message: PREPROCESSING ERROR: Macro definition error: file results/openai/20250417_203249/verification/includes/defender_config.h line 52: results/openai/20250417_203249/verification/includes/defender_config.h:52:13: warning: 'LogError' macro redefined [-Wmacro-redefined]; file results/openai/20250417_203249/verification/includes/defender_config.h line 54: results/openai/20250417_203249/verification/includes/defender_config.h:54:13: warning: 'LogWarn' macro redefined [-Wmacro-redefined]
Suggestions: Fix macro definitions and ensure they are properly defined

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
  - Version 1: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v1.c
  - Version 2: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v2.c
  - Version 3: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v3.c
  - Version 4: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v4.c
  - Version 5: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v5.c
  - Version 6: results/openai/20250417_203249/harnesses/pattern:defender.c:switch/v6.c
  - Size evolution: Initial 27 lines → Final 82 lines (+55 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v1_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v1_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v2_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v2_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v3_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v3_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v4_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v4_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v5_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v5_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v6_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v6_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v7_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v7_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v8_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v8_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v9_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v9_report.md
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v10_results.txt
  - results/openai/20250417_203249/verification/pattern:defender.c:switch/v10_report.md