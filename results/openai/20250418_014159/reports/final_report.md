# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 31.65 seconds
Processed 3 source files.
Analyzed 10 functions.
Identified 8 functions with memory or arithmetic operations.
Generated 8 verification harnesses.
Performed 8 harness refinements (average 1.00 per function).

## File Analysis

### defender.c
Functions analyzed: 8
Functions verified: 8
Successful verifications: 8
Failed verifications: 0

## RAG Knowledge Base Statistics
Code functions stored: 15
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
Functions with full coverage: 7 of 8
Functions without errors: 0 of 8

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Coverage Matrix by Function and Version

The table below shows the coverage metrics for each function across different versions of the generated harnesses:

| Function | Version 1 ||
| --- | Total | Func |
| defender.c:Defender_GetTopic | 95.83% | 91.30% |
| defender.c:Defender_MatchTopic | 97.18% | 95.74% |
| defender.c:extractThingNameLength | 100.00% | 100.00% |
| defender.c:getTopicLength | 100.00% | 100.00% |
| defender.c:matchApi | 100.00% | 100.00% |
| defender.c:matchBridge | 100.00% | 100.00% |
| defender.c:matchPrefix | 100.00% | 100.00% |
| defender.c:writeFormatAndSuffix | 100.00% | 100.00% |

**Note:** 'Total' shows the percentage of all reachable lines that were covered during verification. 'Func' shows the percentage of target function lines that were covered.

## Performance Metrics
Average harness generation time: 3.48 seconds
Average verification time: 0.42 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html

## Summary of Results

### Function: Defender_GetTopic (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 91.30%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:Defender_GetTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:Defender_GetTopic/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:Defender_GetTopic/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:Defender_GetTopic/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:Defender_GetTopic/v2_report.md

### Function: Defender_MatchTopic (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 95.74%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:Defender_MatchTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:Defender_MatchTopic/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:Defender_MatchTopic/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:Defender_MatchTopic/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:Defender_MatchTopic/v2_report.md

### Function: extractThingNameLength (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:extractThingNameLength/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:extractThingNameLength/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:extractThingNameLength/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:extractThingNameLength/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:extractThingNameLength/v2_report.md

### Function: getTopicLength (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:getTopicLength/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:getTopicLength/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:getTopicLength/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:getTopicLength/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:getTopicLength/v2_report.md

### Function: matchApi (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:matchApi/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:matchApi/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchApi/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:matchApi/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchApi/v2_report.md

### Function: matchBridge (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:matchBridge/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:matchBridge/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchBridge/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:matchBridge/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchBridge/v2_report.md

### Function: matchPrefix (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:matchPrefix/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:matchPrefix/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchPrefix/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:matchPrefix/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:matchPrefix/v2_report.md

### Function: writeFormatAndSuffix (File: defender.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_014159/harnesses/defender.c:writeFormatAndSuffix/v1.c

#### Verification Reports: 
  - results/openai/20250418_014159/verification/defender.c:writeFormatAndSuffix/v1_results.txt
  - results/openai/20250418_014159/verification/defender.c:writeFormatAndSuffix/v1_report.md
  - results/openai/20250418_014159/verification/defender.c:writeFormatAndSuffix/v2_results.txt
  - results/openai/20250418_014159/verification/defender.c:writeFormatAndSuffix/v2_report.md