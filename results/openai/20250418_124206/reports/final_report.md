# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 839.26 seconds
Processed 5 source files.
Analyzed 85 functions.
Identified 32 functions with memory or arithmetic operations.
Generated 32 verification harnesses.
Performed 42 harness refinements (average 1.31 per function).

## File Analysis

### core_json.c
Functions analyzed: 32
Functions verified: 32
Successful verifications: 31
Failed verifications: 1

## RAG Knowledge Base Statistics
Code functions stored: 93
Pattern templates: 16
Error patterns stored: 11
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 0
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 0
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 1 of 32
Functions without errors: 0 of 32

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Detailed Coverage Matrix by Function and Version

The table below shows detailed metrics for each function across different versions of the generated harnesses:

| Function | Version 1 |||| Version 2 |||| Version 3 |||| Version 4 |||| Version 5 |||| Version 6 |||| Version 7 |||| Version 8 |||| Version 9 |||| Version 10 |||
| --- | Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors |
| core_json.c:JSON_Iterate | - | - | - || 90.00% | 85.19% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:JSON_SearchConst | 92.59% | 80.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:JSON_SearchT | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:JSON_Validate | 94.44% | 89.47% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:arraySearch | 44.74% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:countHighBits | 30.00% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:hexToInt | 15.79% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:multiSearch | 34.62% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:nextKeyValuePair | 55.10% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:nextValue | 52.78% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:shortestUTF8 | 22.73% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipAnyLiteral | 53.57% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipAnyScalar | 58.06% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipArrayScalars | 57.14% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipCollection | 24.00% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipDecimals | 65.22% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipDigits | 54.55% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipEscape | 39.47% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipExponent | 52.38% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipHexEscape | 44.83% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipLiteral | 70.83% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipNumber | 46.88% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipObjectScalars | 37.50% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipOneHexEscape | 43.75% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipQueryPart | 51.85% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipScalars | 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A |
| core_json.c:skipSpace | 76.19% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipSpaceAndComma | 55.56% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipString | 41.67% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipUTF8 | 62.50% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:skipUTF8MultiByte | 40.54% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_json.c:strnEq | 72.22% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |

**Metrics Legend:**
- **Total %**: Percentage of all reachable lines that were covered during verification.
- **Func %**: Percentage of target function lines that were covered.
- **Errors**: Number of verification errors or failures detected.

## Performance Metrics
Average harness generation time: 5.60 seconds
Average verification time: 14.53 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html

## Summary of Results

### Function: JSON_Iterate (File: core_json.c)
Status: SUCCESS
Refinements: 2
Message: Verification successful
Suggestions: Consider simplifying the harness to improve verification speed and prevent future timeouts

#### Coverage Metrics
- Function coverage: 85.19%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:JSON_Iterate/v1.c
  - Version 2: results/openai/20250418_124206/harnesses/core_json.c:JSON_Iterate/v2.c
  - Size evolution: Initial 62 lines → Final 43 lines (-19 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v2_report.md
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v3_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_Iterate/v3_report.md

### Function: JSON_SearchConst (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful
Suggestions: Consider simplifying the harness to improve verification speed and prevent future timeouts

#### Coverage Metrics
- Function coverage: 80.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:JSON_SearchConst/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchConst/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchConst/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchConst/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchConst/v2_report.md

### Function: JSON_SearchT (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful
Suggestions: Consider simplifying the harness to improve verification speed and prevent future timeouts

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:JSON_SearchT/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchT/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchT/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchT/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_SearchT/v2_report.md

### Function: JSON_Validate (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful
Suggestions: Consider simplifying the harness to improve verification speed and prevent future timeouts

#### Coverage Metrics
- Function coverage: 89.47%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:JSON_Validate/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:JSON_Validate/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_Validate/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:JSON_Validate/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:JSON_Validate/v2_report.md

### Function: arraySearch (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:arraySearch/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:arraySearch/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:arraySearch/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:arraySearch/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:arraySearch/v2_report.md

### Function: countHighBits (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:countHighBits/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:countHighBits/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:countHighBits/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:countHighBits/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:countHighBits/v2_report.md

### Function: hexToInt (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:hexToInt/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:hexToInt/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:hexToInt/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:hexToInt/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:hexToInt/v2_report.md

### Function: multiSearch (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:multiSearch/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:multiSearch/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:multiSearch/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:multiSearch/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:multiSearch/v2_report.md

### Function: nextKeyValuePair (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:nextKeyValuePair/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:nextKeyValuePair/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:nextKeyValuePair/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:nextKeyValuePair/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:nextKeyValuePair/v2_report.md

### Function: nextValue (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:nextValue/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:nextValue/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:nextValue/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:nextValue/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:nextValue/v2_report.md

### Function: shortestUTF8 (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:shortestUTF8/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:shortestUTF8/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:shortestUTF8/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:shortestUTF8/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:shortestUTF8/v2_report.md

### Function: skipAnyLiteral (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipAnyLiteral/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipAnyLiteral/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipAnyLiteral/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipAnyLiteral/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipAnyLiteral/v2_report.md

### Function: skipAnyScalar (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipAnyScalar/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipAnyScalar/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipAnyScalar/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipAnyScalar/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipAnyScalar/v2_report.md

### Function: skipArrayScalars (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipArrayScalars/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipArrayScalars/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipArrayScalars/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipArrayScalars/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipArrayScalars/v2_report.md

### Function: skipCollection (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipCollection/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipCollection/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipCollection/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipCollection/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipCollection/v2_report.md

### Function: skipDecimals (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipDecimals/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipDecimals/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipDecimals/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipDecimals/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipDecimals/v2_report.md

### Function: skipDigits (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipDigits/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipDigits/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipDigits/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipDigits/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipDigits/v2_report.md

### Function: skipEscape (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipEscape/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipEscape/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipEscape/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipEscape/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipEscape/v2_report.md

### Function: skipExponent (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipExponent/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipExponent/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipExponent/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipExponent/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipExponent/v2_report.md

### Function: skipHexEscape (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipHexEscape/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipHexEscape/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipHexEscape/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipHexEscape/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipHexEscape/v2_report.md

### Function: skipLiteral (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipLiteral/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipLiteral/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipLiteral/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipLiteral/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipLiteral/v2_report.md

### Function: skipNumber (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipNumber/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipNumber/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipNumber/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipNumber/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipNumber/v2_report.md

### Function: skipObjectScalars (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipObjectScalars/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipObjectScalars/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipObjectScalars/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipObjectScalars/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipObjectScalars/v2_report.md

### Function: skipOneHexEscape (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipOneHexEscape/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipOneHexEscape/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipOneHexEscape/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipOneHexEscape/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipOneHexEscape/v2_report.md

### Function: skipQueryPart (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipQueryPart/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipQueryPart/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipQueryPart/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipQueryPart/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipQueryPart/v2_report.md

### Function: skipScalars (File: core_json.c)
Status: FAILED
Refinements: 10
Message: PREPROCESSING ERROR: GCC preprocessing failed - check for syntax errors
Suggestions: Fix syntax errors and ensure all necessary includes are available

#### Coverage Metrics
- Function coverage: 0.00%

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v10): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v1.c
  - Version 2: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v2.c
  - Version 3: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v3.c
  - Version 4: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v4.c
  - Version 5: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v5.c
  - Version 6: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v6.c
  - Version 7: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v7.c
  - Version 8: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v8.c
  - Version 9: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v9.c
  - Version 10: results/openai/20250418_124206/harnesses/core_json.c:skipScalars/v10.c
  - Size evolution: Initial 40 lines → Final 156 lines (+116 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v2_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v3_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v3_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v4_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v4_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v5_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v5_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v6_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v6_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v7_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v7_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v8_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v8_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v9_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v9_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v10_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v10_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v11_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipScalars/v11_report.md

### Function: skipSpace (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipSpace/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipSpace/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipSpace/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipSpace/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipSpace/v2_report.md

### Function: skipSpaceAndComma (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipSpaceAndComma/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipSpaceAndComma/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipSpaceAndComma/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipSpaceAndComma/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipSpaceAndComma/v2_report.md

### Function: skipString (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipString/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipString/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipString/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipString/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipString/v2_report.md

### Function: skipUTF8 (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipUTF8/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8/v2_report.md

### Function: skipUTF8MultiByte (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:skipUTF8MultiByte/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8MultiByte/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8MultiByte/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8MultiByte/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:skipUTF8MultiByte/v2_report.md

### Function: strnEq (File: core_json.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_124206/harnesses/core_json.c:strnEq/v1.c

#### Verification Reports: 
  - results/openai/20250418_124206/verification/core_json.c:strnEq/v1_results.txt
  - results/openai/20250418_124206/verification/core_json.c:strnEq/v1_report.md
  - results/openai/20250418_124206/verification/core_json.c:strnEq/v2_results.txt
  - results/openai/20250418_124206/verification/core_json.c:strnEq/v2_report.md