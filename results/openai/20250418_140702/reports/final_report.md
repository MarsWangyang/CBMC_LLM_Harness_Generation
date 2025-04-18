# CBMC Harness Generation Complete - Directory Mode - Openai

Total processing time: 423.32 seconds
Processed 3 source files.
Analyzed 14 functions.
Identified 12 functions with memory or arithmetic operations.
Generated 12 verification harnesses.
Performed 30 harness refinements (average 2.50 per function).

## File Analysis

### fleet_provisioning.c
Functions analyzed: 12
Functions verified: 12
Successful verifications: 10
Failed verifications: 2

## RAG Knowledge Base Statistics
Code functions stored: 18
Pattern templates: 16
Error patterns stored: 20
Successful solutions: 0

The RAG (Retrieval-Augmented Generation) knowledge base stores code functions, patterns, errors, and solutions to improve harness generation over time. Each run contributes to this knowledge base, helping future runs generate better harnesses with fewer iterations.

## Unit Proof Metrics Summary
Total reachable lines: 0
Total coverage: 0.00%
Total reachable lines for harnessed functions only: 0
Coverage of harnessed functions only: 0.00%
Number of reported errors: 0
Functions with full coverage: 2 of 12
Functions without errors: 0 of 12

### Note on Error Reporting:
- Errors are grouped by line number (one error per line)
- Errors about missing function bodies are excluded
- Loop unwinding assertions are excluded from error count

## Detailed Coverage Matrix by Function and Version

The table below shows detailed metrics for each function across different versions of the generated harnesses:

| Function | Version 1 |||| Version 2 |||| Version 3 |||| Version 4 |||| Version 5 |||| Version 6 |||| Version 7 |||| Version 8 |||| Version 9 |||| Version 10 |||
| --- | Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors || Total % | Func % | Errors |
| fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:FleetProvisioning_MatchTopic | 100.00% | 100.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:GetRegisterThingTopicCheckParams | 75.76% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:consumeIfMatch | 62.22% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:consumeTemplateName | 66.67% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:getRegisterThingTopicLength | 36.36% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:parseCreateCertificateFromCsrTopic | 41.67% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:parseCreateKeysAndCertificateTopic | 41.67% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:parseRegisterThingTopic | 31.25% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |
| fleet_provisioning.c:parseTopicFormatSuffix | 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A |
| fleet_provisioning.c:parseTopicSuffix | 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A || 0.00% | 0.00% | N/A |
| fleet_provisioning.c:writeTopicFragmentAndAdvance | 77.78% | 0.00% | N/A || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - || - | - | - |

**Metrics Legend:**
- **Total %**: Percentage of all reachable lines that were covered during verification.
- **Func %**: Percentage of target function lines that were covered.
- **Errors**: Number of verification errors or failures detected.

## Performance Metrics
Average harness generation time: 11.50 seconds
Average verification time: 0.48 seconds
Average evaluation time: 0.00 seconds

## Coverage Analysis
Coverage report available at: coverage/coverage_report.html

## Summary of Results

### Function: FleetProvisioning_GetRegisterThingTopic (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_GetRegisterThingTopic/v2_report.md

### Function: FleetProvisioning_MatchTopic (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 100.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:FleetProvisioning_MatchTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_MatchTopic/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_MatchTopic/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_MatchTopic/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:FleetProvisioning_MatchTopic/v2_report.md

### Function: GetRegisterThingTopicCheckParams (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:GetRegisterThingTopicCheckParams/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:GetRegisterThingTopicCheckParams/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:GetRegisterThingTopicCheckParams/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:GetRegisterThingTopicCheckParams/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:GetRegisterThingTopicCheckParams/v2_report.md

### Function: consumeIfMatch (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:consumeIfMatch/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeIfMatch/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeIfMatch/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeIfMatch/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeIfMatch/v2_report.md

### Function: consumeTemplateName (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:consumeTemplateName/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeTemplateName/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeTemplateName/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeTemplateName/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:consumeTemplateName/v2_report.md

### Function: getRegisterThingTopicLength (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:getRegisterThingTopicLength/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:getRegisterThingTopicLength/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:getRegisterThingTopicLength/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:getRegisterThingTopicLength/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:getRegisterThingTopicLength/v2_report.md

### Function: parseCreateCertificateFromCsrTopic (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseCreateCertificateFromCsrTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateCertificateFromCsrTopic/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateCertificateFromCsrTopic/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateCertificateFromCsrTopic/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateCertificateFromCsrTopic/v2_report.md

### Function: parseCreateKeysAndCertificateTopic (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseCreateKeysAndCertificateTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateKeysAndCertificateTopic/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateKeysAndCertificateTopic/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateKeysAndCertificateTopic/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseCreateKeysAndCertificateTopic/v2_report.md

### Function: parseRegisterThingTopic (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseRegisterThingTopic/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseRegisterThingTopic/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseRegisterThingTopic/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseRegisterThingTopic/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseRegisterThingTopic/v2_report.md

### Function: parseTopicFormatSuffix (File: fleet_provisioning.c)
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
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v1.c
  - Version 2: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v2.c
  - Version 3: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v3.c
  - Version 4: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v4.c
  - Version 5: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v5.c
  - Version 6: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v6.c
  - Version 7: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v7.c
  - Version 8: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v8.c
  - Version 9: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v9.c
  - Version 10: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicFormatSuffix/v10.c
  - Size evolution: Initial 45 lines → Final 223 lines (+178 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v2_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v3_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v3_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v4_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v4_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v5_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v5_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v6_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v6_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v7_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v7_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v8_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v8_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v9_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v9_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v10_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v10_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v11_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicFormatSuffix/v11_report.md

### Function: parseTopicSuffix (File: fleet_provisioning.c)
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
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v1.c
  - Version 2: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v2.c
  - Version 3: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v3.c
  - Version 4: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v4.c
  - Version 5: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v5.c
  - Version 6: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v6.c
  - Version 7: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v7.c
  - Version 8: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v8.c
  - Version 9: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v9.c
  - Version 10: results/openai/20250418_140702/harnesses/fleet_provisioning.c:parseTopicSuffix/v10.c
  - Size evolution: Initial 38 lines → Final 243 lines (+205 lines)
  - Refinement result: Some issues remain after 10 refinements

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v2_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v3_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v3_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v4_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v4_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v5_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v5_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v6_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v6_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v7_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v7_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v8_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v8_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v9_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v9_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v10_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v10_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v11_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:parseTopicSuffix/v11_report.md

### Function: writeTopicFragmentAndAdvance (File: fleet_provisioning.c)
Status: SUCCESS
Refinements: 1
Message: Verification successful

#### Coverage Metrics
- Function coverage: 0.00%

#### Harness Evolution:
  - Version 1: results/openai/20250418_140702/harnesses/fleet_provisioning.c:writeTopicFragmentAndAdvance/v1.c

#### Verification Reports: 
  - results/openai/20250418_140702/verification/fleet_provisioning.c:writeTopicFragmentAndAdvance/v1_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:writeTopicFragmentAndAdvance/v1_report.md
  - results/openai/20250418_140702/verification/fleet_provisioning.c:writeTopicFragmentAndAdvance/v2_results.txt
  - results/openai/20250418_140702/verification/fleet_provisioning.c:writeTopicFragmentAndAdvance/v2_report.md