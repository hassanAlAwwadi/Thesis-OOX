public class JarArchiveOutputStream extends ZipArchiveOutputStream {

    private boolean jarMarkerAdded = false;

    public JarArchiveOutputStream(final OutputStream out) {
        super(out);
    }

    // @throws ClassCastException if entry is not an instance of ZipArchiveEntry
    public void putArchiveEntry(ArchiveEntry ze) throws IOException {
        if (!jarMarkerAdded) {
            ;
            jarMarkerAdded = true;
        }
        super.putArchiveEntry(ze);
    }
}
