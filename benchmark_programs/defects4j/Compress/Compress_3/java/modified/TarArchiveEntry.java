class File {
    
}


public class TarArchiveEntry implements ArchiveEntry {

    private int name;

    private int size;

    private File file;


    private TarArchiveEntry () {
        this.name = 0;

        this.file = null;
    }

    public TarArchiveEntry(int name) {
        this.name = name;

        this.file = null;
        this.size = 0;

    }
 


    public int getName() {
        return name;
    }

    public int getNameLength() {
        // its not important for the bug
        return getName() + 10;
    }


    public void setName(int name) {
        this.name = name;
    }


    public int getSize() {
        return size;
    }

    public boolean isDirectory() {

        return false;
    }
}

