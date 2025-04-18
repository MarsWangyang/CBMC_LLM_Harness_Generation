# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 130.17 seconds
Processed 3 source files.
Analyzed 16 functions.
Identified 13 functions with memory or arithmetic operations.
Generated 13 verification harnesses.
Performed 13 harness refinements (average 1.00 per function).

## File Analysis

### shadow.c
Functions analyzed: 13
Functions verified: 13
Successful verifications: 13
Failed verifications: 0

## RAG Knowledge Base Statistics
Code functions stored: 21
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
Functions with full coverage: 2 of 13
Functions without errors: 0 of 13

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Detailed Coverage Matrix by Function and Version

The table below shows detailed metrics for each function across different versions of the generated harnesses:

| Function | Version 1 |||
| --- | Total % | Func % | Errors |
| shadow.c:Shadow_AssembleTopicString | 100.00% | 100.00% | N/A |
| shadow.c:Shadow_MatchTopic | 100.00% | 100.00% | N/A |
| shadow.c:Shadow_MatchTopicString | 74.67% | 55.81% | N/A |
| shadow.c:containsSubString | 72.00% | 0.00% | N/A |
| shadow.c:createShadowTopicString | 61.82% | 0.00% | N/A |
| shadow.c:extractShadowMessageType | 45.16% | 0.00% | N/A |
| shadow.c:extractShadowRootAndName | 38.10% | 0.00% | N/A |
| shadow.c:extractThingName | 60.00% | 0.00% | N/A |
| shadow.c:getShadowOperationLength | 10.00% | 0.00% | N/A |
| shadow.c:getShadowOperationString | 10.00% | 0.00% | N/A |
| shadow.c:validateAssembleTopicParameters | 71.11% | 0.00% | N/A |
| shadow.c:validateMatchTopicParameters | 77.78% | 0.00% | N/A |
| shadow.c:validateName | 42.86% | 0.00% | N/A |

**Metrics Legend:**
- **Total %**: Percentage of all reachable lines that were covered during verification.
- **Func %**: Percentage of target function lines that were covered.
- **Errors**: Number of verification errors or failures detected.

## Performance Metrics
Average harness generation time: 9.56 seconds
Average verification time: 0.38 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html

## Summary of Results

### Function: Shadow_AssembleTopicString (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:Shadow_AssembleTopicString/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:Shadow_AssembleTopicString/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_AssembleTopicString/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:Shadow_AssembleTopicString/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_AssembleTopicString/v2_report.md

### Function: Shadow_MatchTopic (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:Shadow_MatchTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopic/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopic/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopic/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopic/v2_report.md

### Function: Shadow_MatchTopicString (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 55.81%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:Shadow_MatchTopicString/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopicString/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopicString/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopicString/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:Shadow_MatchTopicString/v2_report.md

### Function: containsSubString (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:containsSubString/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:containsSubString/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:containsSubString/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:containsSubString/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:containsSubString/v2_report.md

### Function: createShadowTopicString (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:createShadowTopicString/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:createShadowTopicString/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:createShadowTopicString/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:createShadowTopicString/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:createShadowTopicString/v2_report.md

### Function: extractShadowMessageType (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:extractShadowMessageType/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:extractShadowMessageType/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractShadowMessageType/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:extractShadowMessageType/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractShadowMessageType/v2_report.md

### Function: extractShadowRootAndName (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:extractShadowRootAndName/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:extractShadowRootAndName/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractShadowRootAndName/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:extractShadowRootAndName/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractShadowRootAndName/v2_report.md

### Function: extractThingName (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:extractThingName/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:extractThingName/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractThingName/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:extractThingName/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:extractThingName/v2_report.md

### Function: getShadowOperationLength (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:getShadowOperationLength/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationLength/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationLength/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationLength/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationLength/v2_report.md

### Function: getShadowOperationString (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:getShadowOperationString/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationString/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationString/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationString/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:getShadowOperationString/v2_report.md

### Function: validateAssembleTopicParameters (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:validateAssembleTopicParameters/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:validateAssembleTopicParameters/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateAssembleTopicParameters/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:validateAssembleTopicParameters/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateAssembleTopicParameters/v2_report.md

### Function: validateMatchTopicParameters (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:validateMatchTopicParameters/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:validateMatchTopicParameters/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateMatchTopicParameters/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:validateMatchTopicParameters/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateMatchTopicParameters/v2_report.md

### Function: validateName (File: shadow.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140125/harnesses/shadow.c:validateName/v1.c

#### Verification Reports: 
  - results/openai/20250418_140125/verification/shadow.c:validateName/v1_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateName/v1_report.md
  - results/openai/20250418_140125/verification/shadow.c:validateName/v2_results.txt
  - results/openai/20250418_140125/verification/shadow.c:validateName/v2_report.md