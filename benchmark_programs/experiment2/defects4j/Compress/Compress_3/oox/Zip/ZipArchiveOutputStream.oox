class ZipArchiveOutputStream implements ArchiveOutputStream {
    ZipArchiveEntry entry;
    OutputStream out;

    ZipArchiveOutputStream(OutputStream out) {
        this.out := out;
        this.entry := null;
    }

    void finish() {
        ZipArchiveEntry entry := this.entry;
        if (entry != null) {
            throw "new IOException(This archives contains unclosed entries.)";
        }
    }

    void closeArchiveEntry() {
        ZipArchiveEntry entry := this.entry;
        if (entry == null) {
            return;
        }
        this.entry := null;
    }

    void putArchiveEntry(ArchiveEntry archiveEntry) {
        this.closeArchiveEntry();
        this.entry := (ZipArchiveEntry) archiveEntry;
    }
}