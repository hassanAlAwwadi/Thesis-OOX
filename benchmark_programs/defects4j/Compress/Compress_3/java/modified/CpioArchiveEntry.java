
public class CpioArchiveEntry implements CpioConstants, ArchiveEntry {

    // Header description fields - should be same throughout an archive
    
    /**
     * See {@link CpioArchiveEntry#setFormat(short)} for possible values.
     */
    private final short fileFormat; 

    /** The number of bytes in each header record; depends on the file format */
    private final int headerSize;

    /** The boundary to which the header and data elements are aligned: 0, 2 or 4 bytes */
    private final int alignmentBoundary;

    private long filesize = 0;
    
    private long chksum = 0;


    public CpioArchiveEntry(final short format) {
        switch (format) {
        case FORMAT_NEW:
            this.headerSize = 110;
            this.alignmentBoundary = 4;
            break;
        case FORMAT_NEW_CRC:
            this.headerSize = 110;
            this.alignmentBoundary = 4;
            break;
        case FORMAT_OLD_ASCII:
            this.headerSize = 76;
            this.alignmentBoundary = 0;
            break;
        case FORMAT_OLD_BINARY:
            this.headerSize = 26;
            this.alignmentBoundary = 2;
            break;
        default:
            throw new IllegalArgumentException("Unknown header type");
        }
        this.fileFormat = format;
    }

    /**
     * Ceates a CPIOArchiveEntry with a specified name. The format of this entry
     * will be the new format.
     * 
     * @param name
     *            The name of this entry.
     */
    public CpioArchiveEntry(final String name) {
        this(FORMAT_NEW);
        this.name = name;
    }

    /**
     * Creates a CPIOArchiveEntry with a specified name. The format of this entry
     * will be the new format.
     * 
     * @param name
     *            The name of this entry.
     * @param size
     *            The size of this entry
     */
    public CpioArchiveEntry(final String name, final long size) {
        this(FORMAT_NEW);
        this.name = name;
        this.setSize(size);
    }

    public CpioArchiveEntry(File inputFile, String entryName) {
        this(entryName, inputFile.isFile() ? inputFile.length() : 0);
        long mode=0;
        if (inputFile.isDirectory()){
            mode |= C_ISDIR;
        } else if (inputFile.isFile()){
            mode |= C_ISREG;
        } else {
            throw new IllegalArgumentException("Cannot determine type of file "+inputFile.getName());
        }
        // TODO set other fields as needed
        setMode(mode);
    }

    /**
     * Check if the method is allowed for the defined format.
     */
    private void checkNewFormat() {
        if ((this.fileFormat & FORMAT_NEW_MASK) == 0) {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Check if the method is allowed for the defined format.
     */
    private void checkOldFormat() {
        if ((this.fileFormat & FORMAT_OLD_MASK) == 0) {
            throw new UnsupportedOperationException();
        }
    }

    /**
     * Get the checksum.
     * Only supported for the new formats.
     * 
     * @return Returns the checksum.
     * @throws UnsupportedOperationException if the format is not a new format
     */
    public long getChksum() {
        checkNewFormat();
        return this.chksum;
    }

    /**
     * Get the device id.
     * 
     * @return Returns the device id.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with a new
     *             format.
     */
    public long getDevice() {
        checkOldFormat();
        return this.min;
    }

    /**
     * Get the major device id.
     * 
     * @return Returns the major device id.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with an old
     *             format.
     */
    public long getDeviceMaj() {
        checkNewFormat();
        return this.maj;
    }

    /**
     * Get the minor device id
     * 
     * @return Returns the minor device id.
     * @throws UnsupportedOperationException if format is not a new format
     */
    public long getDeviceMin() {
        checkNewFormat();
        return this.min;
    }

    /**
     * Get the filesize.
     * 
     * @return Returns the filesize.
     * @see org.apache.commons.compress.archivers.ArchiveEntry#getSize()
     */
    public long getSize() {
        return this.filesize;
    }

    public short getFormat() {
        return this.fileFormat;
    }

    /**
     * Get the group id.
     * 
     * @return Returns the group id.
     */
    public long getGID() {
        return this.gid;
    }

    /**
     * Get the header size for this CPIO format
     * 
     * @return Returns the header size in bytes.
     */
    public int getHeaderSize() {
        return this.headerSize;
    }

    /**
     * Get the alignment boundary for this CPIO format
     * 
     * @return Returns the aligment boundary (0, 2, 4) in bytes
     */
    public int getAlignmentBoundary() {
        return this.alignmentBoundary;
    }

    /**
     * Get the number of bytes needed to pad the header to the alignment boundary.
     * 
     * @return the number of bytes needed to pad the header (0,1,2,3)
     */
    public int getHeaderPadCount(){
        if (this.alignmentBoundary == 0) return 0;
        int size = this.headerSize+this.name.length()+1; // Name has terminating null
        int remain = size % this.alignmentBoundary;
        if (remain > 0){
            return this.alignmentBoundary - remain;
        }
        return 0;
    }

    /**
     * Get the number of bytes needed to pad the data to the alignment boundary.
     * 
     * @return the number of bytes needed to pad the data (0,1,2,3)
     */
    public int getDataPadCount(){
        if (this.alignmentBoundary == 0) return 0;
        long size = this.filesize;
        int remain = (int) (size % this.alignmentBoundary);
        if (remain > 0){
            return this.alignmentBoundary - remain;
        }
        return 0;
    }

    /**
     * Set the inode.
     * 
     * @return Returns the inode.
     */
    public long getInode() {
        return this.inode;
    }

    /**
     * Get the mode of this entry (e.g. directory, regular file).
     * 
     * @return Returns the mode.
     */
    public long getMode() {
        return this.mode;
    }

    /**
     * Get the name.
     * 
     * @return Returns the name.
     */
    public String getName() {
        return this.name;
    }

    /**
     * Get the number of links.
     * 
     * @return Returns the number of links.
     */
    public long getNumberOfLinks() {
        return this.nlink;
    }

    /**
     * Get the remote device id.
     * 
     * @return Returns the remote device id.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with a new
     *             format.
     */
    public long getRemoteDevice() {
        checkOldFormat();
        return this.rmin;
    }

    /**
     * Get the remote major device id.
     * 
     * @return Returns the remote major device id.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with an old
     *             format.
     */
    public long getRemoteDeviceMaj() {
        checkNewFormat();
        return this.rmaj;
    }

    /**
     * Get the remote minor device id.
     * 
     * @return Returns the remote minor device id.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with an old
     *             format.
     */
    public long getRemoteDeviceMin() {
        checkNewFormat();
        return this.rmin;
    }

    /**
     * Get the time in seconds.
     * 
     * @return Returns the time.
     */
    public long getTime() {
        return this.mtime;
    }

    /**
     * Get the user id.
     * 
     * @return Returns the user id.
     */
    public long getUID() {
        return this.uid;
    }

    /**
     * Check if this entry represents a block device.
     * 
     * @return TRUE if this entry is a block device.
     */
    public boolean isBlockDevice() {
        return (this.mode & S_IFMT) == C_ISBLK;
    }

    /**
     * Check if this entry represents a character device.
     * 
     * @return TRUE if this entry is a character device.
     */
    public boolean isCharacterDevice() {
        return (this.mode & S_IFMT) == C_ISCHR;
    }

    /**
     * Check if this entry represents a directory.
     * 
     * @return TRUE if this entry is a directory.
     */
    public boolean isDirectory() {
        return (this.mode & S_IFMT) == C_ISDIR;
    }

    /**
     * Check if this entry represents a network device.
     * 
     * @return TRUE if this entry is a network device.
     */
    public boolean isNetwork() {
        return (this.mode & S_IFMT) == C_ISNWK;
    }

    /**
     * Check if this entry represents a pipe.
     * 
     * @return TRUE if this entry is a pipe.
     */
    public boolean isPipe() {
        return (this.mode & S_IFMT) == C_ISFIFO;
    }

    /**
     * Check if this entry represents a regular file.
     * 
     * @return TRUE if this entry is a regular file.
     */
    public boolean isRegularFile() {
        return (this.mode & S_IFMT) == C_ISREG;
    }

    /**
     * Check if this entry represents a socket.
     * 
     * @return TRUE if this entry is a socket.
     */
    public boolean isSocket() {
        return (this.mode & S_IFMT) == C_ISSOCK;
    }

    /**
     * Check if this entry represents a symbolic link.
     * 
     * @return TRUE if this entry is a symbolic link.
     */
    public boolean isSymbolicLink() {
        return (this.mode & S_IFMT) == C_ISLNK;
    }

    /**
     * Set the checksum. The checksum is calculated by adding all bytes of a
     * file to transfer (crc += buf[pos] & 0xFF).
     * 
     * @param chksum
     *            The checksum to set.
     */
    public void setChksum(final long chksum) {
        checkNewFormat();
        this.chksum = chksum;
    }

    /**
     * Set the device id.
     * 
     * @param device
     *            The device id to set.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with a new
     *             format.
     */
    public void setDevice(final long device) {
        checkOldFormat();
        this.min = device;
    }

    /**
     * Set major device id.
     * 
     * @param maj
     *            The major device id to set.
     */
    public void setDeviceMaj(final long maj) {
        checkNewFormat();
        this.maj = maj;
    }

    /**
     * Set the minor device id
     * 
     * @param min
     *            The minor device id to set.
     */
    public void setDeviceMin(final long min) {
        checkNewFormat();
        this.min = min;
    }

    /**
     * Set the filesize.
     * 
     * @param size
     *            The filesize to set.
     */
    public void setSize(final long size) {
        if (size < 0 || size > 0xFFFFFFFFL) {
            throw new IllegalArgumentException("invalid entry size <" + size
                    + ">");
        }
        this.filesize = size;
    }

    /**
     * Set the group id.
     * 
     * @param gid
     *            The group id to set.
     */
    public void setGID(final long gid) {
        this.gid = gid;
    }

    /**
     * Set the inode.
     * 
     * @param inode
     *            The inode to set.
     */
    public void setInode(final long inode) {
        this.inode = inode;
    }

    /**
     * Set the mode of this entry (e.g. directory, regular file).
     * 
     * @param mode
     *            The mode to set.
     */
    public void setMode(final long mode) {
        final long maskedMode = mode & S_IFMT;
        switch ((int) maskedMode) {
        case C_ISDIR:
        case C_ISLNK:
        case C_ISREG:
        case C_ISFIFO:
        case C_ISCHR:
        case C_ISBLK:
        case C_ISSOCK:
        case C_ISNWK:
            break;
        default:
            throw new IllegalArgumentException(
                    "Unknown mode. "
                    + "Full: " + Long.toHexString(mode) 
                    + " Masked: " + Long.toHexString(maskedMode));
        }

        this.mode = mode;
    }

    /**
     * Set the name.
     * 
     * @param name
     *            The name to set.
     */
    public void setName(final String name) {
        this.name = name;
    }

    /**
     * Set the number of links.
     * 
     * @param nlink
     *            The number of links to set.
     */
    public void setNumberOfLinks(final long nlink) {
        this.nlink = nlink;
    }

    /**
     * Set the remote device id.
     * 
     * @param device
     *            The remote device id to set.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with a new
     *             format.
     */
    public void setRemoteDevice(final long device) {
        checkOldFormat();
        this.rmin = device;
    }

    /**
     * Set the remote major device id.
     * 
     * @param rmaj
     *            The remote major device id to set.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with an old
     *             format.
     */
    public void setRemoteDeviceMaj(final long rmaj) {
        checkNewFormat();
        this.rmaj = rmaj;
    }

    /**
     * Set the remote minor device id.
     * 
     * @param rmin
     *            The remote minor device id to set.
     * @throws UnsupportedOperationException
     *             if this method is called for a CPIOArchiveEntry with an old
     *             format.
     */
    public void setRemoteDeviceMin(final long rmin) {
        checkNewFormat();
        this.rmin = rmin;
    }

    /**
     * Set the time in seconds.
     * 
     * @param time
     *            The time to set.
     */
    public void setTime(final long time) {
        this.mtime = time;
    }

    /**
     * Set the user id.
     * 
     * @param uid
     *            The user id to set.
     */
    public void setUID(final long uid) {
        this.uid = uid;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#hashCode()
     */
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((name == null) ? 0 : name.hashCode());
        return result;
    }

    /* (non-Javadoc)
     * @see java.lang.Object#equals(java.lang.Object)
     */
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        CpioArchiveEntry other = (CpioArchiveEntry) obj;
        if (name == null) {
            if (other.name != null) {
                return false;
            }
        } else if (!name.equals(other.name)) {
            return false;
        }
        return true;
    }
}
