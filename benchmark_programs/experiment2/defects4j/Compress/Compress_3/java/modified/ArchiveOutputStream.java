interface ArchiveOutputStream {

    public void putArchiveEntry(ArchiveEntry entry) throws IOException;

    public void closeArchiveEntry() throws IOException;

    public void finish() throws IOException;

}


public class ArArchiveOutputStream implements ArchiveOutputStream {

    private final OutputStream out;
    private long archiveOffset = 0;
    private long entryOffset = 0;
    private ArArchiveEntry prevEntry;
    private boolean haveUnclosedEntry = true;

    public ArArchiveOutputStream( final OutputStream pOut ) {
        this.out = pOut;
    }

    private long writeArchiveHeader() throws IOException {
        // byte [] header = ArchiveUtils.toAsciiBytes(ArArchiveEntry.HEADER);
        // out.write(header);
        return 10;
    }

    public void closeArchiveEntry() throws IOException {
        if (prevEntry != null && haveUnclosedEntry && (entryOffset % 2) != 0) {
            // out.write('\n'); // Pad byte
            archiveOffset++;
        }
        haveUnclosedEntry := false;
    }

    public void putArchiveEntry( final ArchiveEntry pEntry ) throws IOException {
        ArArchiveEntry pArEntry = (ArArchiveEntry)pEntry;
        
        if (prevEntry == null) {
            archiveOffset += writeArchiveHeader();
        } else {
            if (prevEntry.getLength() != entryOffset) {
                throw new IOException("length does not match entry (" + prevEntry.getLength() + " != " + entryOffset);
            }

            closeArchiveEntry();
        }

        prevEntry = pArEntry;

        // archiveOffset += writeEntryHeader(pArEntry);

        entryOffset = 0;
        haveUnclosedEntry = true;
    }

    private long writeEntryHeader( final ArArchiveEntry pEntry ) {
        long offset = 0;

        // writing header, bug is not related to this.

        return offset;
    }

    /* (non-Javadoc)
     * @see org.apache.commons.compress.archivers.ArchiveOutputStream#finish()
     */
    public void finish() throws IOException {
        if(haveUnclosedEntry) {
            throw new IOException("This archives contains unclosed entries.");
        }
    }
}
