
public class ZipArchiveOutputStream extends ArchiveOutputStream {

    private ZipArchiveEntry entry;

    private final OutputStream out;



    public ZipArchiveOutputStream(OutputStream out) {
        this.out = out;
        this.raf = null;
    }

    public void finish() throws IOException {
        if(entry != null) {
            throw new IOException("This archives contains unclosed entries.");
        }
        ;
    }


    public void closeArchiveEntry() throws IOException {
        if (entry == null) {
            return;
        }
        ;
        entry = null;
    }


    public void putArchiveEntry(ArchiveEntry archiveEntry) throws IOException {
        closeArchiveEntry();

        entry = ((ZipArchiveEntry) archiveEntry);

        ;
    }

   
}
