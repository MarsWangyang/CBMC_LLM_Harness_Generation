void harness() {
    TransportInterface_t *pTransport = malloc(sizeof(TransportInterface_t));
    if (pTransport != NULL) {
        pTransport->send = nondet_bool() ? send : NULL;
        pTransport->recv = nondet_bool() ? recv : NULL;
    }

    HTTPRequestHeaders_t *pRequestHeaders = malloc(sizeof(HTTPRequestHeaders_t));
    if (pRequestHeaders != NULL) {
        pRequestHeaders->pBuffer = malloc(sizeof(char));
        pRequestHeaders->headersLen = nondet_size_t();
        pRequestHeaders->bufferLen = nondet_size_t();
    }

    size_t reqBodyBufLen = nondet_size_t();
    uint8_t *pRequestBodyBuf = malloc(reqBodyBufLen);

    HTTPResponse_t *pResponse = malloc(sizeof(HTTPResponse_t));
    if (pResponse != NULL) {
        pResponse->pBuffer = malloc(sizeof(char));
        pResponse->bufferLen = nondet_size_t();
        pResponse->getTime = nondet_bool() ? getTime : NULL;
    }

    uint32_t sendFlags = nondet_uint32_t();

    HTTPStatus_t returnStatus = HTTPClient_Send(pTransport, pRequestHeaders, pRequestBodyBuf, reqBodyBufLen, pResponse, sendFlags);

    assert(returnStatus == HTTPInvalidParameter || returnStatus == HTTPSuccess);
}