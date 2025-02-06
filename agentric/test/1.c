HTTPStatus_t HTTPClient_Send( const TransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t sendFlags )
{
    HTTPStatus_t returnStatus = HTTPInvalidParameter;

    if( pTransport == NULL )
    {
        LogError( ( "Parameter check failed: pTransport interface is NULL." ) );
    }
    else if( pTransport->send == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->send is NULL." ) );
    }
    else if( pTransport->recv == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->recv is NULL." ) );
    }
    else if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
    }
    else if( pRequestHeaders->headersLen < HTTP_MINIMUM_REQUEST_LINE_LENGTH )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen "
                    "does not meet minimum the required length. "
                    "MinimumRequiredLength=%u, HeadersLength=%lu",
                    HTTP_MINIMUM_REQUEST_LINE_LENGTH,
                    ( unsigned long ) ( pRequestHeaders->headersLen ) ) );
    }
    else if( pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen > "
                    "pRequestHeaders->bufferLen." ) );
    }
    else if( pResponse == NULL )
    {
        LogError( ( "Parameter check failed: pResponse is NULL. " ) );
    }
    else if( pResponse->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pResponse->pBuffer is NULL." ) );
    }
    else if( pResponse->bufferLen == 0U )
    {
        LogError( ( "Parameter check failed: pResponse->bufferLen is zero." ) );
    }
    else if( ( pRequestBodyBuf == NULL ) && ( reqBodyBufLen > 0U ) )
    {
        /* If there is no body to send we must ensure that the reqBodyBufLen is
         * zero so that no Content-Length header is automatically written. */
        LogError( ( "Parameter check failed: pRequestBodyBuf is NULL, but "
                    "reqBodyBufLen is greater than zero." ) );
    }
    else if( reqBodyBufLen > ( size_t ) ( INT32_MAX ) )
    {
        /* This check is needed because convertInt32ToAscii() is used on the
         * reqBodyBufLen to create a Content-Length header value string. */
        LogError( ( "Parameter check failed: reqBodyBufLen > INT32_MAX."
                    "reqBodyBufLen=%lu",
                    ( unsigned long ) reqBodyBufLen ) );
    }
    else
    {
        if( pResponse->getTime == NULL )
        {
            /* Set a zero timestamp function when the application did not configure
             * one. */
            pResponse->getTime = getZeroTimestampMs;
        }

        returnStatus = HTTPSuccess;
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = sendHttpRequest( pTransport,
                                        pResponse->getTime,
                                        pRequestHeaders,
                                        pRequestBodyBuf,
                                        reqBodyBufLen,
                                        sendFlags );
    }

    if( returnStatus == HTTPSuccess )
    {
        returnStatus = HTTPClient_ReceiveAndParseHttpResponse( pTransport,
                                                               pResponse,
                                                               pRequestHeaders );
    }

    return returnStatus;
}
