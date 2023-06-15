


public class TarArchiveOutputStream extends ArchiveOutputStream {
    /** Fail if a long file name is required in the archive. */
    public static final int LONGFILE_ERROR = 0;

    /** Long paths will be truncated in the archive. */
    public static final int LONGFILE_TRUNCATE = 1;

    /** GNU tar extensions are used to store long file names in the archive. */
    public static final int LONGFILE_GNU = 2;

    private long      currSize;
    private String    currName;
    private long      currBytes;
    // private final byte[]    recordBuf;
    private int       assemLen;
    // private final byte[]    assemBuf;
    // protected final TarBuffer buffer;
    private int       longFileMode = LONGFILE_ERROR;

    private boolean closed = false;
    
    private final OutputStream out;

  
    public TarArchiveOutputStream(OutputStream os) {
        this.out = os;
        int blockSize = 512 * 20;
        int recordSize = 512;

        // this.buffer = new TarBuffer(os, blockSize, recordSize);
        this.assemLen = 0;
        // this.assemBuf = new byte[recordSize];
        // this.recordBuf = new byte[recordSize];
        this.longFileMode = 0;
    }

    public void finish() throws IOException {
    }

    
    public void putArchiveEntry(ArchiveEntry archiveEntry) throws IOException {
        TarArchiveEntry entry = (TarArchiveEntry) archiveEntry;
        if (entry.getNameLength() >= 100) {

            if (longFileMode == LONGFILE_GNU) {
                // create a TarEntry for the LongLink, the contents
                // of which are the entry's name
                TarArchiveEntry longLinkEntry = new TarArchiveEntry("././@LongLink");

                // final byte[] nameBytes = entry.getName().getBytes(); // TODO is it correct to use the default charset here?
                // longLinkEntry.setSize(nameBytes.length + 1); // +1 for NUL
                putArchiveEntry(longLinkEntry);
                // write(nameBytes);
                // write(0); // NUL terminator
                closeArchiveEntry();
            } else if (longFileMode != LONGFILE_TRUNCATE) {
                throw new RuntimeException("file name '" + entry.getName()
                                           + "' is too long ( > "
                                           + 100 + " bytes)");
            }
        }

        // entry.writeEntryHeader(recordBuf);
        // buffer.writeRecord(recordBuf);

        currBytes = 0;

        if (entry.isDirectory()) {
            currSize = 0;
        } else {
            currSize = entry.getSize();
        }
        currName = entry.getName();
    }


    public void closeArchiveEntry() throws IOException {
        if (assemLen > 0) {
            // for (int i = assemLen; i < assemBuf.length; ++i) {
            //     assemBuf[i] = 0;
            // }

            // buffer.writeRecord(assemBuf);

            currBytes += assemLen;
            assemLen = 0;
        }

        if (currBytes < currSize) {
            throw new IOException("entry '" + currName + "' closed at '"
                                  + currBytes
                                  + "' before the '" + currSize
                                  + "' bytes specified in the header were written");
        }
    }


    // public void write(byte[] wBuf, int wOffset, int numToWrite) throws IOException {
    public void write(int wOffset, int numToWrite) throws IOException {
        if ((currBytes + numToWrite) > currSize) {
            throw new IOException("request to write '" + numToWrite
                                  + "' bytes exceeds size in header of '"
                                  + currSize + "' bytes for entry '"
                                  + currName + "'");
        }

        while (numToWrite > 0) {
            ;
        }
    }
  
    private void writeEOFRecord() throws IOException {
        for (int i = 0; i < recordBuf.length; ++i) {
            // recordBuf[i] = 0;
        }

        // buffer.writeRecord(recordBuf);
    }

}
