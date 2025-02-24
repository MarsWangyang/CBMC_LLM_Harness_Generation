void harness()
{
    NetworkEndPoint_t * pxEndPoint = allocate(sizeof(NetworkEndPoint_t));
    BaseType_t xReset;
    BaseType_t xDoCheck;
    if(pxEndPoint != NULL)
    {
        // assume_ABOOL(xReset);
        // assume_ABOOL(xDoCheck);
        vDHCPProcess(xReset, pxEndPoint);
    }
}