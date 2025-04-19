# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 3958.81 seconds
Processed 23 source files.
Analyzed 223 functions.
Identified 35 functions with memory or arithmetic operations.
Generated 35 verification harnesses.
Performed 133 harness refinements (average 3.80 per function).

## File Analysis

### core_http_client.c
Functions analyzed: 35
Functions verified: 35
Successful verifications: 30
Failed verifications: 5

## RAG Knowledge Base Statistics
Code functions stored: 247
Pattern templates: 16
Error patterns stored: 103
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 0
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 0
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 21 of 35
Functions without errors: 0 of 35

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Detailed Coverage Matrix by Function and Version

The table below shows detailed metrics for each function across different versions of the generated harnesses:

| Function | Version 1 |||| Version 2 |||| Version 3 |||| Version 4 |||| Version 5 |||| Version 6 |||| Version 7 |||| Version 8 |||| Version 9 |||| Version 10 |||
| --- | Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors |
| core_http_client.c:HTTPClient_AddHeader | 86.79% | 73.08% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_AddRangeHeader | 81.82% | 62.96% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_InitializeRequestHeaders | 96.94% | 94.00% | N/A || 96.88% | 94.00% | N/A || - | - | - || 64.29% | 40.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_ReadHeader | 86.54% | 76.67% | N/A || 86.00% | 76.67% | N/A || 84.78% | 76.67% | N/A || 72.92% | 56.67% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse | - | - | - || 0.00% | 0.00% | N/A || 95.74% | 91.84% | N/A || 95.74% | 91.84% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_Send | - | - | - || 0.00% | 0.00% | N/A || - | - | - || 0.00% | 0.00% | N/A || - | - | - || 0.00% | 0.00% | N/A || 93.20% | 41.38% | N/A || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_SendHttpData | 0.00% | 0.00% | N/A || 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:HTTPClient_SendHttpHeaders | - | - | - || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A |
| core_http_client.c:HTTPClient_strerror | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:addContentLengthHeader | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 80.95% | 78.57% | N/A || 50.00% | 78.57% | N/A || 42.86% | 78.57% | N/A || 54.84% | 78.57% | N/A || 59.26% | 78.57% | N/A || 54.84% | 78.57% | N/A || 52.94% | 78.57% | N/A || 41.86% | 78.57% | N/A |
| core_http_client.c:addHeader | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:addRangeHeader | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 91.89% | 92.86% | N/A || 91.89% | 92.86% | N/A || 21.43% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:caseInsensitiveStringCmp | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:convertInt32ToAscii | 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 92.59% | 81.82% | N/A || 90.38% | 81.82% | N/A || 90.57% | 81.82% | N/A || 90.57% | 81.82% | N/A || 91.30% | 81.82% | N/A || - | - | - || - | - | - |
| core_http_client.c:findHeaderFieldParserCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:findHeaderInResponse | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:findHeaderOnHeaderCompleteCallback | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:findHeaderValueParserCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:getFinalResponseStatus | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpHeaderStrncpy | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnBodyCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnHeaderFieldCallback | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 94.87% | 88.24% | N/A || - | - | - |
| core_http_client.c:httpParserOnHeaderValueCallback | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnHeadersCompleteCallback | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnMessageBeginCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnMessageCompleteCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnStatusCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:httpParserOnStatusCompleteCallback | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:initializeParsingContextForFirstResponse | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:parseHttpResponse | 92.86% | 88.89% | N/A || 94.74% | 88.89% | N/A || 95.77% | 88.89% | N/A || 95.89% | 88.89% | N/A || 95.71% | 88.89% | N/A || 96.30% | 88.89% | N/A || 96.59% | 88.89% | N/A || 86.02% | 51.85% | N/A || - | - | - || - | - | - |
| core_http_client.c:processCompleteHeader | 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A |
| core_http_client.c:processLlhttpError | 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:sendHttpBody | 0.00% | 0.00% | N/A || - | - | - || 0.00% | 0.00% | N/A || - | - | - || 0.00% | 0.00% | N/A || - | - | - || 0.00% | 0.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A || 100.00% | 100.00% | N/A |
| core_http_client.c:sendHttpRequest | 0.00% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| core_http_client.c:writeRequestLine | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |

**Metrics Legend:**
- **Total %**: Percentage of all reachable lines that were covered during verification.
- **Func %**: Percentage of target function lines that were covered.
- **Errors**: Number of verification errors or failures detected.

## Performance Metrics
Average harness generation time: 8.77 seconds
Average verification time: 7.47 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html

## Summary of Results

### Function: HTTPClient_AddHeader (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 73.08%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_AddHeader/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddHeader/v2_report.md

### Function: HTTPClient_AddRangeHeader (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 62.96%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_AddRangeHeader/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddRangeHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddRangeHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddRangeHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_AddRangeHeader/v2_report.md

### Function: HTTPClient_InitializeRequestHeaders (File: core_http_client.c)
Status: SUCCESS
Refinements: 4
Message: Verification successful

#### Coverage Metrics
- Function coverage: 40.00%

#### Coverage Evolution
- Initial coverage (v1): 94.00%
- Final coverage (v4): 40.00%
- Coverage improvement: -54.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4.c
  - Size evolution: Initial 95 lines → Final 63 lines (-32 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_InitializeRequestHeaders/v5_report.md

### Function: HTTPClient_ReadHeader (File: core_http_client.c)
Status: SUCCESS
Refinements: 4
Message: Verification successful

#### Coverage Metrics
- Function coverage: 56.67%

#### Coverage Evolution
- Initial coverage (v1): 76.67%
- Final coverage (v4): 56.67%
- Coverage improvement: -20.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReadHeader/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReadHeader/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReadHeader/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReadHeader/v4.c
  - Size evolution: Initial 55 lines → Final 49 lines (-6 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReadHeader/v5_report.md

### Function: HTTPClient_ReceiveAndParseHttpResponse (File: core_http_client.c)
Status: SUCCESS
Refinements: 4
Message: Verification successful

#### Coverage Metrics
- Function coverage: 91.84%

#### Coverage Evolution
- Initial coverage (v2): 0.00%
- Final coverage (v4): 91.84%
- Coverage improvement: 91.84%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4.c
  - Size evolution: Initial 45 lines → Final 95 lines (+50 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_ReceiveAndParseHttpResponse/v5_report.md

### Function: HTTPClient_Send (File: core_http_client.c)
Status: SUCCESS
Refinements: 7
Message: Verification successful

#### Coverage Metrics
- Function coverage: 41.38%

#### Coverage Evolution
- Initial coverage (v2): 0.00%
- Final coverage (v7): 41.38%
- Coverage improvement: 41.38%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_Send/v7.c
  - Size evolution: Initial 141 lines → Final 325 lines (+184 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_Send/v8_report.md

### Function: HTTPClient_SendHttpData (File: core_http_client.c)
Status: SUCCESS
Refinements: 2
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v2): 100.00%
- Coverage improvement: 100.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpData/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpData/v2.c
  - Size evolution: Initial 40 lines → Final 74 lines (+34 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpData/v3_report.md

### Function: HTTPClient_SendHttpHeaders (File: core_http_client.c)
Status: FAILED
Refinements: 10
Message: VERIFICATION FAILED: Unspecified verification error
Suggestions: Review the full verification output for details

#### Coverage Metrics
- Function coverage: 0.00%

#### Coverage Evolution
- Initial coverage (v2): 0.00%
- Final coverage (v10): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v9.c
  - Version 10: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_SendHttpHeaders/v10.c
  - Size evolution: Initial 46 lines → Final 160 lines (+114 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v10_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v11_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_SendHttpHeaders/v11_report.md

### Function: HTTPClient_strerror (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:HTTPClient_strerror/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_strerror/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_strerror/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_strerror/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:HTTPClient_strerror/v2_report.md

### Function: addContentLengthHeader (File: core_http_client.c)
Status: FAILED
Refinements: 10
Message: VERIFICATION FAILED: Null pointer dereference detected
Suggestions: Add null pointer checks before dereferencing pointers

#### Coverage Metrics
- Function coverage: 78.57%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v10): 78.57%
- Coverage improvement: -21.43%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v9.c
  - Version 10: results/openai/20250418_112814/harnesses/core_http_client.c:addContentLengthHeader/v10.c
  - Size evolution: Initial 20 lines → Final 57 lines (+37 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v10_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v11_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addContentLengthHeader/v11_report.md

### Function: addHeader (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:addHeader/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:addHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addHeader/v2_report.md

### Function: addRangeHeader (File: core_http_client.c)
Status: SUCCESS
Refinements: 5
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v5): 0.00%
- Coverage improvement: -100.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:addRangeHeader/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:addRangeHeader/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:addRangeHeader/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:addRangeHeader/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:addRangeHeader/v5.c
  - Size evolution: Initial 29 lines → Final 59 lines (+30 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:addRangeHeader/v6_report.md

### Function: caseInsensitiveStringCmp (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:caseInsensitiveStringCmp/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:caseInsensitiveStringCmp/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:caseInsensitiveStringCmp/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:caseInsensitiveStringCmp/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:caseInsensitiveStringCmp/v2_report.md

### Function: convertInt32ToAscii (File: core_http_client.c)
Status: SUCCESS
Refinements: 8
Message: Verification successful

#### Coverage Metrics
- Function coverage: 81.82%

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v8): 81.82%
- Coverage improvement: 81.82%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:convertInt32ToAscii/v8.c
  - Size evolution: Initial 23 lines → Final 64 lines (+41 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:convertInt32ToAscii/v9_report.md

### Function: findHeaderFieldParserCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderFieldParserCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderFieldParserCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderFieldParserCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderFieldParserCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderFieldParserCallback/v2_report.md

### Function: findHeaderInResponse (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderInResponse/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderInResponse/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderInResponse/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderInResponse/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderInResponse/v2_report.md

### Function: findHeaderOnHeaderCompleteCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 3
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v3): 100.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderOnHeaderCompleteCallback/v3.c
  - Size evolution: Initial 25 lines → Final 34 lines (+9 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderOnHeaderCompleteCallback/v4_report.md

### Function: findHeaderValueParserCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:findHeaderValueParserCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderValueParserCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderValueParserCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderValueParserCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:findHeaderValueParserCallback/v2_report.md

### Function: getFinalResponseStatus (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:getFinalResponseStatus/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:getFinalResponseStatus/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:getFinalResponseStatus/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:getFinalResponseStatus/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:getFinalResponseStatus/v2_report.md

### Function: httpHeaderStrncpy (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpHeaderStrncpy/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpHeaderStrncpy/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpHeaderStrncpy/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpHeaderStrncpy/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpHeaderStrncpy/v2_report.md

### Function: httpParserOnBodyCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnBodyCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnBodyCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnBodyCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnBodyCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnBodyCallback/v2_report.md

### Function: httpParserOnHeaderFieldCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 9
Message: Verification successful

#### Coverage Metrics
- Function coverage: 88.24%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v9): 88.24%
- Coverage improvement: -11.76%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderFieldCallback/v9.c
  - Size evolution: Initial 83 lines → Final 57 lines (-26 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderFieldCallback/v10_report.md

### Function: httpParserOnHeaderValueCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 2
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v2): 100.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeaderValueCallback/v2.c
  - Size evolution: Initial 54 lines → Final 63 lines (+9 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeaderValueCallback/v3_report.md

### Function: httpParserOnHeadersCompleteCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 7
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v7): 100.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnHeadersCompleteCallback/v7.c
  - Size evolution: Initial 80 lines → Final 82 lines (+2 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnHeadersCompleteCallback/v8_report.md

### Function: httpParserOnMessageBeginCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnMessageBeginCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageBeginCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageBeginCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageBeginCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageBeginCallback/v2_report.md

### Function: httpParserOnMessageCompleteCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnMessageCompleteCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnMessageCompleteCallback/v2_report.md

### Function: httpParserOnStatusCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnStatusCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCallback/v2_report.md

### Function: httpParserOnStatusCompleteCallback (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:httpParserOnStatusCompleteCallback/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:httpParserOnStatusCompleteCallback/v2_report.md

### Function: initializeParsingContextForFirstResponse (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:initializeParsingContextForFirstResponse/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:initializeParsingContextForFirstResponse/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:initializeParsingContextForFirstResponse/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:initializeParsingContextForFirstResponse/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:initializeParsingContextForFirstResponse/v2_report.md

### Function: parseHttpResponse (File: core_http_client.c)
Status: SUCCESS
Refinements: 8
Message: Verification successful

#### Coverage Metrics
- Function coverage: 51.85%

#### Coverage Evolution
- Initial coverage (v1): 88.89%
- Final coverage (v8): 51.85%
- Coverage improvement: -37.04%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:parseHttpResponse/v8.c
  - Size evolution: Initial 40 lines → Final 140 lines (+100 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:parseHttpResponse/v9_report.md

### Function: processCompleteHeader (File: core_http_client.c)
Status: FAILED
Refinements: 10
Message: VERIFICATION FAILED: Unspecified verification error
Suggestions: Review the full verification output for details

#### Coverage Metrics
- Function coverage: 0.00%

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v10): 0.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v9.c
  - Version 10: results/openai/20250418_112814/harnesses/core_http_client.c:processCompleteHeader/v10.c
  - Size evolution: Initial 82 lines → Final 229 lines (+147 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v10_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v11_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processCompleteHeader/v11_report.md

### Function: processLlhttpError (File: core_http_client.c)
Status: SUCCESS
Refinements: 3
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 100.00%
- Final coverage (v3): 100.00%
- Coverage improvement: 0.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:processLlhttpError/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:processLlhttpError/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:processLlhttpError/v3.c
  - Size evolution: Initial 16 lines → Final 22 lines (+6 lines)
  - Refinement result: Successfully addressed all verification issues

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:processLlhttpError/v4_report.md

### Function: sendHttpBody (File: core_http_client.c)
Status: FAILED
Refinements: 10
Message: VERIFICATION FAILED: Null pointer dereference detected
Suggestions: Add null pointer checks before dereferencing pointers

#### Coverage Metrics
- Function coverage: 100.00%

#### Coverage Evolution
- Initial coverage (v1): 0.00%
- Final coverage (v10): 100.00%
- Coverage improvement: 100.00%
- Error reduction: 0

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v9.c
  - Version 10: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpBody/v10.c
  - Size evolution: Initial 44 lines → Final 70 lines (+26 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v10_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v11_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpBody/v11_report.md

### Function: sendHttpRequest (File: core_http_client.c)
Status: TIMEOUT
Refinements: 10
Message: CBMC verification timed out after 180 seconds.
Suggestions: The function may have complex paths requiring longer verification time. Consider using more selective file inclusion or increasing timeout.

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v1.c
  - Version 2: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v2.c
  - Version 3: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v3.c
  - Version 4: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v4.c
  - Version 5: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v5.c
  - Version 6: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v6.c
  - Version 7: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v7.c
  - Version 8: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v8.c
  - Version 9: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v9.c
  - Version 10: results/openai/20250418_112814/harnesses/core_http_client.c:sendHttpRequest/v10.c
  - Size evolution: Initial 66 lines → Final 72 lines (+6 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v2_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v3_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v3_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v4_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v4_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v5_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v5_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v6_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v6_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v7_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v7_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v8_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v8_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v9_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v9_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v10_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v10_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v11_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:sendHttpRequest/v11_report.md

### Function: writeRequestLine (File: core_http_client.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_112814/harnesses/core_http_client.c:writeRequestLine/v1.c

#### Verification Reports: 
  - results/openai/20250418_112814/verification/core_http_client.c:writeRequestLine/v1_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:writeRequestLine/v1_report.md
  - results/openai/20250418_112814/verification/core_http_client.c:writeRequestLine/v2_results.txt
  - results/openai/20250418_112814/verification/core_http_client.c:writeRequestLine/v2_report.md