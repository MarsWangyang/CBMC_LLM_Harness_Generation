void harness() {
    TransportInterface_t *pTransport = malloc(sizeof(TransportInterface_t));
    if (pTransport != NULL) {
        pTransport->send = nondet_bool() ? send : NULL;
        pTransport->recv = nondet_bool() ? recv : NULL;
        __CPROVER_assume(pTransport->send != NULL || pTransport->recv != NULL);
    }

    HTTPRequestHeaders_t *pRequestHeaders = malloc(sizeof(HTTPRequestHeaders_t));
    if (pRequestHeaders != NULL) {
        pRequestHeaders->pBuffer = malloc(HTTP_MINIMUM_REQUEST_LINE_LENGTH);
        pRequestHeaders->headersLen = nondet_size_t();
        pRequestHeaders->bufferLen = nondet_size_t();
        __CPROVER_assume(pRequestHeaders->headersLen >= HTTP_MINIMUM_REQUEST_LINE_LENGTH);
        __CPROVER_assume(pRequestHeaders->headersLen <= pRequestHeaders->bufferLen);
    }

    size_t reqBodyBufLen = nondet_size_t();
    __CPROVER_assume(reqBodyBufLen <= INT32_MAX);
    uint8_t *pRequestBodyBuf = NULL;
    if (reqBodyBufLen > 0) {
        pRequestBodyBuf = malloc(reqBodyBufLen);
        __CPROVER_assume(pRequestBodyBuf != NULL);
    }

    HTTPResponse_t *pResponse = malloc(sizeof(HTTPResponse_t));
    if (pResponse != NULL) {
        pResponse->pBuffer = malloc(HTTP_MINIMUM_REQUEST_LINE_LENGTH);
        pResponse->bufferLen = nondet_size_t();
        __CPROVER_assume(pResponse->bufferLen > 0);
        pResponse->getTime = nondet_bool() ? getTime : getZeroTimestampMs;
    }

    uint32_t sendFlags = nondet_uint32_t();

    HTTPStatus_t returnStatus = HTTPClient_Send(pTransport, pRequestHeaders, pRequestBodyBuf, reqBodyBufLen, pResponse, sendFlags);

    assert(returnStatus == HTTPInvalidParameter || returnStatus == HTTPSuccess);
}