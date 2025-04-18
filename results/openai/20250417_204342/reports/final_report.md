# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 5678.63 seconds
Processed 23 source files.
Analyzed 223 functions.
Identified 39 functions with memory or arithmetic operations.
Generated 39 verification harnesses.
Performed 241 harness refinements (average 6.18 per function).

## File Analysis

### core_http_client.c
Functions analyzed: 35
Functions verified: 35
Successful verifications: 12
Failed verifications: 23

### pattern
Functions analyzed: 4
Functions verified: 4
Successful verifications: 2
Failed verifications: 2

## RAG Knowledge Base Statistics
Code functions stored: 247
Pattern templates: 16
Error patterns stored: 227
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 39
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 39
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 0 of 39
Functions without errors: 39 of 39

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Coverage Matrix by Function and Version

The table below shows the coverage metrics for each function across different versions of the generated harnesses:

| Function | Version 1 ||| Version 2 ||| Version 3 ||| Version 4 ||| Version 5 ||| Version 6 ||| Version 7 ||| Version 8 ||| Version 9 ||
| --- | Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func || Total | Func |
| core_http_client.c:HTTPClient_AddHeader | 74.42% | 57.69% || 70.45% | 50.00% || 71.11% | 50.00% || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:HTTPClient_AddRangeHeader | 80.49% | 70.37% || 68.18% | 48.15% || 68.18% | 48.15% || 69.57% | 48.15% || 68.18% | 48.15% || 68.18% | 48.15% || 68.18% | 48.15% || 68.18% | 48.15% || 68.18% | 48.15% |
| core_http_client.c:HTTPClient_InitializeRequestHeaders | 93.33% | 92.00% || 81.16% | 74.00% || 81.69% | 74.00% || 83.12% | 74.00% || 83.12% | 74.00% || 83.12% | 74.00% || 83.12% | 74.00% || 83.12% | 74.00% || 83.12% | 74.00% |
| core_http_client.c:HTTPClient_ReadHeader | 79.07% | 70.00% || 79.07% | 70.00% || 81.63% | 70.00% || 80.85% | 70.00% || 80.85% | 70.00% || 80.85% | 70.00% || 80.85% | 70.00% || 80.85% | 70.00% || 80.85% | 70.00% |
| core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse | - | - || - | - || - | - || 93.94% | 91.84% || 93.94% | 91.84% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:HTTPClient_SendHttpData | 97.56% | 96.30% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:HTTPClient_SendHttpHeaders | - | - || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:HTTPClient_strerror | 100.00% | 100.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:addContentLengthHeader | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:addHeader | 30.19% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:addRangeHeader | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:caseInsensitiveStringCmp | 41.67% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:convertInt32ToAscii | 26.67% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:findHeaderFieldParserCallback | 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 60.61% | 0.00% || 60.61% | 0.00% || 60.61% | 0.00% || 60.61% | 0.00% || 60.61% | 0.00% || 60.61% | 0.00% |
| core_http_client.c:findHeaderInResponse | 36.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:findHeaderOnHeaderCompleteCallback | 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% || 60.00% | 0.00% |
| core_http_client.c:findHeaderValueParserCallback | 48.72% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% || 50.00% | 0.00% |
| core_http_client.c:getFinalResponseStatus | 38.89% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:httpHeaderStrncpy | 45.71% | 17.39% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:httpParserOnBodyCallback | 51.22% | 0.00% || 51.22% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% || 52.38% | 0.00% |
| core_http_client.c:httpParserOnHeaderFieldCallback | 46.88% | 0.00% || 48.48% | 0.00% || 48.48% | 0.00% || 48.48% | 0.00% || 51.43% | 0.00% || 51.43% | 0.00% || 51.43% | 0.00% || 51.43% | 0.00% || 51.43% | 0.00% |
| core_http_client.c:httpParserOnHeaderValueCallback | 55.56% | 0.00% || 55.56% | 0.00% || 60.00% | 0.00% || 61.29% | 0.00% || 61.29% | 0.00% || 61.29% | 0.00% || 61.29% | 0.00% || 61.29% | 0.00% || 61.29% | 0.00% |
| core_http_client.c:httpParserOnHeadersCompleteCallback | 26.92% | 0.00% || 21.88% | 0.00% || 20.59% | 0.00% || 20.59% | 0.00% || 20.00% | 0.00% || 20.00% | 0.00% || 20.00% | 0.00% || 20.00% | 0.00% || 20.00% | 0.00% |
| core_http_client.c:httpParserOnMessageBeginCallback | 60.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:httpParserOnMessageCompleteCallback | 60.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:httpParserOnStatusCallback | 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% || 59.38% | 0.00% |
| core_http_client.c:httpParserOnStatusCompleteCallback | 53.85% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| core_http_client.c:initializeParsingContextForFirstResponse | 34.48% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% || 36.67% | 0.00% |
| core_http_client.c:parseHttpResponse | 30.77% | 0.00% || 30.77% | 0.00% || 32.50% | 0.00% || 32.50% | 0.00% || 34.15% | 0.00% || 34.15% | 0.00% || 34.15% | 0.00% || 34.15% | 0.00% || 34.15% | 0.00% |
| core_http_client.c:processCompleteHeader | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:processLlhttpError | 11.11% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 16.67% | 0.00% || 18.37% | 0.00% |
| core_http_client.c:sendHttpBody | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:sendHttpRequest | 53.33% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| core_http_client.c:writeRequestLine | 32.61% | 0.00% || 32.61% | 0.00% || 36.73% | 0.00% || 36.73% | 0.00% || 36.73% | 0.00% || 36.73% | 0.00% || 36.73% | 0.00% || 41.51% | 0.00% || 41.51% | 0.00% |
| pattern:core_http_client.c:for | 100.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |
| pattern:core_http_client.c:if | 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% || 0.00% | 0.00% |
| pattern:core_http_client.c:switch | 100.00% | 0.00% || - | - || - | - || - | - || - | - || - | - || - | - || - | - || - | - |

**Note:** 'Total' shows the percentage of all reachable lines that were covered during verification. 'Func' shows the percentage of target function lines that were covered.

## Performance Metrics
Average harness generation time: 6.27 seconds
Average verification time: 11.41 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html
Detailed metrics available in: coverage/coverage_metrics.csv

## Summary of Results

### Function: HTTPClient_AddHeader (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddHeader/v3.c
  - Size evolution: Initial 41 lines → Final 43 lines (+2 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddHeader/v4_report.md

### Function: HTTPClient_AddRangeHeader (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddRangeHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddRangeHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_AddRangeHeader/v3.c
  - Size evolution: Initial 36 lines → Final 48 lines (+12 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_AddRangeHeader/v10_report.md

### Function: HTTPClient_InitializeRequestHeaders (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4.c
  - Size evolution: Initial 28 lines → Final 57 lines (+29 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v10_report.md

### Function: HTTPClient_ReadHeader (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReadHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReadHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReadHeader/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReadHeader/v4.c
  - Size evolution: Initial 46 lines → Final 48 lines (+2 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReadHeader/v10_report.md

### Function: HTTPClient_ReceiveAndParseHttpResponse (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v5.c
  - Version 6: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v6.c
  - Version 7: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v7.c
  - Version 8: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v8.c
  - Size evolution: Initial 37 lines → Final 58 lines (+21 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v10_report.md

### Function: HTTPClient_Send (File: core_http_client.c)
Status: TIMEOUT
Refinements: 9
Message: CBMC verification timed out after 170 seconds.
Suggestions: The function may have complex paths requiring longer verification time. Consider using more selective file inclusion or increasing timeout.

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_Send/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_Send/v2.c
  - Size evolution: Initial 48 lines → Final 61 lines (+13 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_Send/v10_report.md

### Function: HTTPClient_SendHttpData (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpData/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpData/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpData/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpData/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpData/v2_report.md

### Function: HTTPClient_SendHttpHeaders (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v5.c
  - Size evolution: Initial 42 lines → Final 61 lines (+19 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v10_report.md

### Function: HTTPClient_strerror (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:HTTPClient_strerror/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_strerror/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_strerror/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_strerror/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:HTTPClient_strerror/v2_report.md

### Function: addContentLengthHeader (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: PREPROCESSING ERROR: Macro definition error: file results/openai/20250417_204342/verification/harness_files/addContentLengthHeader_harness_v9.c line 10: results/openai/20250417_204342/verification/harness_files/addContentLengthHeader_harness_v9.c:10:43: error: too many arguments provided to function-like macro invocation; file results/openai/20250417_204342/verification/includes/core_http_config_defaults.h line 124: results/openai/20250417_204342/verification/includes/core_http_config_defaults.h:124:13: note: macro 'LogError' defined here
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v5.c
  - Version 6: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v6.c
  - Version 7: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v7.c
  - Version 8: results/openai/20250417_204342/harnesses/core_http_client.c:addContentLengthHeader/v8.c
  - Size evolution: Initial 26 lines → Final 59 lines (+33 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addContentLengthHeader/v10_report.md

### Function: addHeader (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:addHeader/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:addHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addHeader/v2_report.md

### Function: addRangeHeader (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:addRangeHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:addRangeHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:addRangeHeader/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:addRangeHeader/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:addRangeHeader/v5.c
  - Size evolution: Initial 38 lines → Final 51 lines (+13 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:addRangeHeader/v10_report.md

### Function: caseInsensitiveStringCmp (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:caseInsensitiveStringCmp/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:caseInsensitiveStringCmp/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:caseInsensitiveStringCmp/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:caseInsensitiveStringCmp/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:caseInsensitiveStringCmp/v2_report.md

### Function: convertInt32ToAscii (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:convertInt32ToAscii/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:convertInt32ToAscii/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:convertInt32ToAscii/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:convertInt32ToAscii/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:convertInt32ToAscii/v2_report.md

### Function: findHeaderFieldParserCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderFieldParserCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderFieldParserCallback/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderFieldParserCallback/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderFieldParserCallback/v4.c
  - Size evolution: Initial 41 lines → Final 45 lines (+4 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderFieldParserCallback/v10_report.md

### Function: findHeaderInResponse (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderInResponse/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderInResponse/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderInResponse/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderInResponse/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderInResponse/v2_report.md

### Function: findHeaderOnHeaderCompleteCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2.c
  - Size evolution: Initial 29 lines → Final 29 lines (0 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v10_report.md

### Function: findHeaderValueParserCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderValueParserCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:findHeaderValueParserCallback/v2.c
  - Size evolution: Initial 40 lines → Final 45 lines (+5 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:findHeaderValueParserCallback/v10_report.md

### Function: getFinalResponseStatus (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:getFinalResponseStatus/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:getFinalResponseStatus/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:getFinalResponseStatus/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:getFinalResponseStatus/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:getFinalResponseStatus/v2_report.md

### Function: httpHeaderStrncpy (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpHeaderStrncpy/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpHeaderStrncpy/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpHeaderStrncpy/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpHeaderStrncpy/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpHeaderStrncpy/v2_report.md

### Function: httpParserOnBodyCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnBodyCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnBodyCallback/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnBodyCallback/v3.c
  - Size evolution: Initial 43 lines → Final 47 lines (+4 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnBodyCallback/v10_report.md

### Function: httpParserOnHeaderFieldCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v4.c
  - Size evolution: Initial 34 lines → Final 43 lines (+9 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v10_report.md

### Function: httpParserOnHeaderValueCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v4.c
  - Size evolution: Initial 33 lines → Final 44 lines (+11 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeaderValueCallback/v10_report.md

### Function: httpParserOnHeadersCompleteCallback (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v5.c
  - Size evolution: Initial 49 lines → Final 84 lines (+35 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v10_report.md

### Function: httpParserOnMessageBeginCallback (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnMessageBeginCallback/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageBeginCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageBeginCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageBeginCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageBeginCallback/v2_report.md

### Function: httpParserOnMessageCompleteCallback (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnMessageCompleteCallback/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v2_report.md

### Function: httpParserOnStatusCallback (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnStatusCallback/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnStatusCallback/v2.c
  - Size evolution: Initial 40 lines → Final 43 lines (+3 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCallback/v10_report.md

### Function: httpParserOnStatusCompleteCallback (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:httpParserOnStatusCompleteCallback/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v2_report.md

### Function: initializeParsingContextForFirstResponse (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:initializeParsingContextForFirstResponse/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:initializeParsingContextForFirstResponse/v2.c
  - Size evolution: Initial 26 lines → Final 29 lines (+3 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:initializeParsingContextForFirstResponse/v10_report.md

### Function: parseHttpResponse (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:parseHttpResponse/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:parseHttpResponse/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:parseHttpResponse/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:parseHttpResponse/v4.c
  - Size evolution: Initial 37 lines → Final 44 lines (+7 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:parseHttpResponse/v10_report.md

### Function: processCompleteHeader (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:processCompleteHeader/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:processCompleteHeader/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:processCompleteHeader/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:processCompleteHeader/v4.c
  - Size evolution: Initial 47 lines → Final 53 lines (+6 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processCompleteHeader/v10_report.md

### Function: processLlhttpError (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:processLlhttpError/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:processLlhttpError/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:processLlhttpError/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:processLlhttpError/v4.c
  - Size evolution: Initial 19 lines → Final 32 lines (+13 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:processLlhttpError/v10_report.md

### Function: sendHttpBody (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v5.c
  - Version 6: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpBody/v6.c
  - Size evolution: Initial 33 lines → Final 68 lines (+35 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpBody/v10_report.md

### Function: sendHttpRequest (File: core_http_client.c)
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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpRequest/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpRequest/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpRequest/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpRequest/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/core_http_client.c:sendHttpRequest/v5.c
  - Size evolution: Initial 46 lines → Final 69 lines (+23 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:sendHttpRequest/v10_report.md

### Function: writeRequestLine (File: core_http_client.c)
Status: FAILED
Refinements: 9
Message: VERIFICATION FAILED: Memory leak detected
Suggestions: Ensure all allocated memory is freed in all execution paths

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
  - Version 1: results/openai/20250417_204342/harnesses/core_http_client.c:writeRequestLine/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/core_http_client.c:writeRequestLine/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/core_http_client.c:writeRequestLine/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/core_http_client.c:writeRequestLine/v4.c
  - Size evolution: Initial 37 lines → Final 50 lines (+13 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v1_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v1_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v2_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v2_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v3_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v3_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v4_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v4_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v5_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v5_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v6_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v6_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v7_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v7_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v8_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v8_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v9_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v9_report.md
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v10_results.txt
  - results/openai/20250417_204342/verification/core_http_client.c:writeRequestLine/v10_report.md

### Function: core_http_client.c:for (File: pattern)
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
  - Version 1: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:for/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:for/v1_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:for/v1_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:for/v2_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:for/v2_report.md

### Function: core_http_client.c:if (File: pattern)
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
  - Version 1: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:if/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:if/v2.c
  - Size evolution: Initial 79 lines → Final 84 lines (+5 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v1_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v1_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v2_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v2_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v3_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v3_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v4_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v4_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v5_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v5_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v6_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v6_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v7_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v7_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v8_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v8_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v9_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v9_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v10_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:if/v10_report.md

### Function: core_http_client.c:switch (File: pattern)
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
  - Version 1: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:switch/v1.c

#### Verification Reports: 
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:switch/v1_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:switch/v1_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:switch/v2_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:switch/v2_report.md

### Function: core_http_client.c:while (File: pattern)
Status: TIMEOUT
Refinements: 9
Message: CBMC verification timed out after 170 seconds.
Suggestions: The function may have complex paths requiring longer verification time. Consider using more selective file inclusion or increasing timeout.

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
  - Version 1: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v1.c
  - Version 2: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v2.c
  - Version 3: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v3.c
  - Version 4: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v4.c
  - Version 5: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v5.c
  - Version 6: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v6.c
  - Version 7: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v7.c
  - Version 8: results/openai/20250417_204342/harnesses/pattern:core_http_client.c:while/v8.c
  - Size evolution: Initial 77 lines → Final 87 lines (+10 lines)
  - Refinement result: Some issues remain after 9 refinements

#### Verification Reports: 
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v1_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v1_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v2_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v2_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v3_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v3_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v4_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v4_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v5_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v5_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v6_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v6_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v7_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v7_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v8_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v8_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v9_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v9_report.md
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v10_results.txt
  - results/openai/20250417_204342/verification/pattern:core_http_client.c:while/v10_report.md