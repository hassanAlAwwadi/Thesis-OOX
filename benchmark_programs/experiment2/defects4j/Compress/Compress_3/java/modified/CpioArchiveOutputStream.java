
public class CpioArchiveOutputStream extends ArchiveOutputStream implements
        CpioConstants {

    private CpioArchiveEntry entry;

    private boolean closed = false;

    private boolean finished;


    private final short entryFormat;

    private long crc = 0;

    private long written;

    private final OutputStream out;


   
    public CpioArchiveOutputStream(final OutputStream out) {
        this.out = new FilterOutputStream(out);
        this.entryFormat = 1;
    }


    private void ensureOpen() throws IOException {
        if (this.closed) {
            throw new IOException("Stream closed");
        }
    }


    public void putArchiveEntry(ArchiveEntry entry) throws IOException {
        CpioArchiveEntry e = (CpioArchiveEntry) entry;
        ensureOpen();
        if (this.entry != null) {
            closeArchiveEntry(); // close previous entry
        }

        final short format = e.getFormat();
        if (format != this.entryFormat){
            throw new IOException("Header format: "+format+" does not match existing format: "+this.entryFormat);
        }

        // if (this.names.put(e.getName(), e) != null) {
        //     throw new IOException("duplicate entry: " + e.getName());
        // }

        // writeHeader(e);
        this.entry = e;
        this.written = 0;
    }




    public void closeArchiveEntry() throws IOException {
        ensureOpen();

        if (this.entry.getSize() != this.written) {
            throw new IOException("invalid entry size (expected "
                    + this.entry.getSize() + " but got " + this.written
                    + " bytes)");
        }
        
        // if (this.entry.getFormat() == FORMAT_NEW_CRC) {
        //     if (this.crc != this.entry.getChksum()) {
        //         throw new IOException("CRC Error");
        //     }
        // }
        this.entry = null;
        this.crc = 0;
        this.written = 0;
    }


    // public void write(final byte[] b, final int off, final int len)
    // public void write(final int off, final int len)  {
    //     ensureOpen();
    //     if (off < 0 || len < 0) {
    //         throw new IndexOutOfBoundsException();
    //     } else if (len == 0) {
    //         return;
    //     }

    //     if (this.entry == null) {
    //         throw new IOException("no current CPIO entry");
    //     }
    //     if (this.written + len > this.entry.getSize()) {
    //         throw new IOException("attempt to write past end of STORED entry");
    //     }

    //     this.written += len;
    //     if (this.entry.getFormat() == FORMAT_NEW_CRC) {
    //         for (int pos = 0; pos < len; pos++) {
    //             ;
    //         }
    //     }
    // }

    public void finish() throws IOException {
        ensureOpen();

        if (this.finished) {
            return;
        }
        if (this.entry != null) {
            throw new IOException("This archives contains unclosed entries.");
        }
        this.entry = new CpioArchiveEntry(this.entryFormat);
        this.entry.setName(CPIO_TRAILER);
        this.entry.setNumberOfLinks(1);
        // writeHeader(this.entry);
        closeArchiveEntry();
    }

    // public void close() throws IOException {
    //     if (!this.closed) {
    //         this.finish();
    //         out.close();
    //         this.closed = true;
    //     }
    // }



}
