#include <assert.h>
#include <stdint.h>
#include <cbmc_proof/proof_allocators.h>

/* Function under test */
HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
    HTTPRequestHeaders_t * pRequestHeaders,
    const uint8_t * pRequestBodyBuf,
    size_t reqBodyBufLen,
    HTTPResponse_t * pResponse,
    uint32_t sendFlags );

/* Stub for the LogError function. */
void LogError( const char * const pErrString )
{
    assert( pErrString != NULL );
}

/* Stub for the send function. */
int32_t send( const NetworkContext_t * pNetworkContext,
              const void * pBuffer,
              size_t bytesToSend )
{
    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );
    return nondet_int32_t();
}

/* Stub for the recv function. */
int32_t recv( const NetworkContext_t * pNetworkContext,
              void * pBuffer,
              size_t bytesToRecv )
{
    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );
    return nondet_int32_t();
}

/* Stub for the getZeroTimestampMs function. */
uint32_t getZeroTimestampMs( void )
{
    return nondet_uint32_t();
}

void harness()
{
    TransportInterface_t * pTransport = can_fail_malloc(sizeof(TransportInterface_t));
    HTTPRequestHeaders_t * pRequestHeaders = can_fail_malloc(sizeof(HTTPRequestHeaders_t));
    size_t reqBodyBufLen = nondet_size_t();
    uint8_t * pRequestBodyBuf = can_fail_malloc(reqBodyBufLen * sizeof(uint8_t));
    HTTPResponse_t * pResponse = can_fail_malloc(sizeof(HTTPResponse_t));
    uint32_t sendFlags = nondet_uint32_t();

    if (pTransport != NULL) {
        pTransport->send = nondet_bool() ? NULL : send;
        pTransport->recv = nondet_bool() ? NULL : recv;
    }

    if (pRequestHeaders != NULL) {
        pRequestHeaders->bufferLen = nondet_size_t();
        pRequestHeaders->headersLen = nondet_size_t();
        __CPROVER_assume(pRequestHeaders->headersLen <= pRequestHeaders->bufferLen);
        pRequestHeaders->pBuffer = can_fail_malloc(pRequestHeaders->bufferLen * sizeof(uint8_t));
    }

    if (pResponse != NULL) {
        pResponse->bufferLen = nondet_size_t();
        pResponse->pBuffer = can_fail_malloc(pResponse->bufferLen * sizeof(uint8_t));
        pResponse->getTime = nondet_bool() ? NULL : getZeroTimestampMs;
    }

    HTTPStatus_t returnStatus = HTTPClient_Send(pTransport, pRequestHeaders, pRequestBodyBuf, reqBodyBufLen, pResponse, sendFlags);

    /* Check post-conditions */
    if (returnStatus == HTTPSuccess || returnStatus == HTTPNoResponse || returnStatus == HTTPPartialResponse) {
        assert(pTransport != NULL);
        assert(pRequestHeaders != NULL);
        assert(pResponse != NULL);
    }
}