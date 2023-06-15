public class ArchiveStreamFactory {

    public ArchiveOutputStream createArchiveOutputStream(
            final String archiverName, final OutputStream out)
            throws ArchiveException {
        if (archiverName == null || out == null) {
            throw new IllegalArgumentException(
                    "Archivername and stream must not be null.");
        }

        if ("ar".equalsIgnoreCase(archiverName)) {
            return new ArArchiveOutputStream(out);
        } else if ("zip".equalsIgnoreCase(archiverName)) {
            return new ZipArchiveOutputStream(out);
        } else if ("tar".equalsIgnoreCase(archiverName)) {
            return new TarArchiveOutputStream(out);
        } else if ("jar".equalsIgnoreCase(archiverName)) {
            return new JarArchiveOutputStream(out);
        } else if ("cpio".equalsIgnoreCase(archiverName)) {
            return new CpioArchiveOutputStream(out);
        }
        throw new ArchiveException("Archiver: " + archiverName + " not found.");
    }
}
