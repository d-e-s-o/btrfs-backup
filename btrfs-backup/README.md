btrfs-backup
============

Purpose
-------

btrfs-backup is a program that can be used to backup data from one or
multiple btrfs file systems. It relies on the btrfs(8) utility program
to perform its job and provides a very simple interface for quick btrfs
snapshot creation and transferal.

As for the btrfs file system itself, the unit of backup is a subvolume.
Creation of snapshots for subvolumes is performed on an on demand basis,
that is, only if new data is detected to be available on the respective
subvolume a new snapshot is taken.

The program reasons in terms of repositories. A repository is a
directory which is used to contain the newly created as well as already
available snapshots. Usually, this directory would be on another btrfs
file system but btrfs-backup also supports backup to and restoration
from non-btrfs file systems.

In terms of backup there are two repositories involved: a source
repository and a destination repository. These repositories are kept in
sync by performing an incremental transfer of the files of a snapshot
from the source to the destination. On the destination repository, the
snapshot will subsequently be remanifested or stored in a file.


Examples
--------

Assuming the following directory layout where each of the directories is
a btrfs subvolume:                                                <br />
.                                                                 <br />
├── backup                                                        <br />
├── snapshots                                                     <br />
└── subvolume                                                     <br />

The idea is that 'snapshots' will be the source repository, 'backup'
will be the destination repository, and 'subvolume' is the btrfs
subvolume to backup.

### Backup
In order to create a backup, use the following command:

$ btrfs-backup backup --subvolume=subvolume/ snapshots/ backup/

The -s/--subvolume option can be supplied multiple times in order to
perform a backup of multiple subvolumes.

Along with a backup old snapshots can also be deleted in an automated
fashion. The --keep-for option can be given and a duration specified
that defines the duration after which old snapshots are deleted. An
example invocation looks like this:

$ btrfs-backup backup --keep-for=1d
                      --subvolume=subvolume/ snapshots/ backup/

Using the above command, all snapshots older than one day will be purged
from the snapshots/ repository (the backup/ repository is left
untouched). Supported duration units are: seconds (S), minutes (M),
hours (H), days (d), weeks (w), months (m), and years (y).

Note that as a safety measure, the most recent snapshot cannot be
deleted using this option.

### Restore
To restore the latest snapshot for the given subvolume from the backup,
the following command can be used:

$ btrfs-backup restore --subvolume=subvolume/ backup/ snapshots/

Alternatively, you can use the --reverse option to keep the order of the
source and destination repository that was used during backup (as
opposed to restoration). This option exists for convenience only, so
that not the entire command line has to be amended but only one word
replaced and an option appended to convert a backup operation into a
restore operation.

$ btrfs-backup restore --reverse
                       --subvolume=subvolume/ snapshots/ backup/

The above steps for restoration assume that the subvolume you initially
backed up got deleted. However, under certain circumstances it might be
the case that you only want to restore the snapshots (the read-only
subvolumes created below snapshots/ in the example above) as opposed to
the original subvolume (i.e., subvolume/ above). This behavior can be
achieved by means of the snapshots-only option, like so:

$ btrfs-backup restore --snapshots-only
                       --subvolume=subvolume/ backup/ snapshots/

### Remote Execution
In many cases it is a requirement to backup a subvolume to a remote host
(or restore a subvolume from it). Mounting a remote btrfs file system
locally by means of, for instance, sshfs will not provide the ability to
use btrfs specific tools on it.
To that end, commands can be run on the remote host directly (provided
it offers an interface for command execution from the outside and that
is has the required btrfs tool suite installed). A typical example for
remote command execution is SSH. Using btrfs-backup on a remote host by
means of an SSH connection can be achieved with the --remote-cmd option:

$ btrfs-backup backup --remote-cmd='/usr/bin/ssh server'
                      --subvolume=subvolume/ snapshots/ backup/

In this example, we assume that by invoking '/usr/bin/ssh server'
locally we can establish a connection to the remote server. The command
specified using the --remote-cmd option has to be given with the full
path. Furthermore, this command must accept the command to execute
remotely (that is, on the host named 'server' in our example above) as
its arguments. Note that backup/ in this case does not refer to a local
folder but rather one on the remote side.

There are certain cases (an SSH setup with ControlMaster mode enabled
and ControlPersist option set that establishes a new master connection
from within btrfs-backup, for instance) where performing a backup takes
longer than it should or appears to be stalled [1]. In such an event the
--no-read-stderr option can be useful. It works around this issue with
the downside of no error message but only exit codes being available in
the case of command failure.

### Filters
btrfs-backup supports the notion of filters to process the serialized
data stream of a subvolume or incremental changes. Using filters it is
possible to insert arbitrary commands into the post-serialization and
pre-deserialization process. This functionality can be used to apply
compression to the backup process, for example.

The program distinguishes between two filters: a send filter is applied
after serialization of data took place during a backup and a receive
filter takes effect before deserialization in a restore operation. Under
normal circumstances, both filters complement each other with the
receive filter reverting the changes made by the send filter.
An example usage is compression. In a compression scenario the send
filter could be used to compress the data stream and the receive filter
can decompress it again.

Filters can be specified by means of the --send-filter and --recv-filter
options. All filtering commands have to be specified with absolute paths
to the script or binary to invoke as a filter. Multiple filters can be
specified by supplying multiple options. The order in which each of the
send and receive filters is applied equals the order in which the
respective options were given. A sample invocation using gzip and bzip2
for compression and decompression could look like this:

$ btrfs-backup backup --send-filter='/bin/gzip --stdout'
                      --send-filter='/bin/bzip2 --stdout --compress'
                      --recv-filter='/bin/bzip2 --decompress'
                      --recv-filter='/bin/gzip --decompress'
                      --subvolume=subvolume/ snapshots/ backup/

Note that this example is designed to illustrate usage of the filter
options. In a production scenario one would not apply two compression
methods on top of each other. Also, compression is used as an
illustrative example here. Other uses can be thought of (replication and
encryption, for instance). Arguably, compression of the binary data
stream might not result in much savings of bandwidth since it is
reasonable to believe that the btrfs program already creates a
sufficiently compressed stream of data.
Note furthermore that since filters are sensitive to ordering, they have
to be reordered for the restore case unless the --reverse option
(explained above) is used.
Lastly, note that filtering can be combined with remote command
execution as one would naively expect.

###Snapshot Files
Although a subvolume from a btrfs file system is to be backed up, the
file system where the data is stored does not necessarily have to be a
btrfs file system. btrfs-backup supports the notion of file
repositories. Just like ordinary repositories, they contain the backed
up data of a btrfs subvolume or snapshot that can be used to restore the
original subvolume. However, file repositories do not contain the
remanifested subvolume but rather a binary blob of data. This property
is their biggest advantage since it opens up the possibility for
end-to-end encryption: the data can be encrypted at the source (where
the subvolume to back up resides) and be sent to and stored at the
destination in the form of a file.

Snapshot files are identified by an extension. As usual, such an
extension helps identify the content. The extension can be specified
by means of the --snapshot-ext option. This option also tells
btrfs-backup that the backup should be performed to a file repository.
If it is specified, btrfs-backup requires the usage of a send and
receiver filter, for the restore and backup case, respectively. The
receive filter needs to read data from a file whereas the send filter
needs to write into a file. In order to convey the actual file name to
the filter, the user has to include a special string, "{file}" (without
the quotation marks), in the first send filter and the last receive
filter. Subsequently, btrfs-backup will replace this string with the
actual file name and invoke the filter command.

An example invocation to create a backup could look like this:

$ btrfs-backup backup --snapshot-ext='bin'
                      --recv-filter='/bin/dd of={file}'
                      --subvolume=subvolume/ snapshots/ backup/

Instead of remanifesting the subvolume in the backup/ folder, the data
is dumped into a .bin file.

Similarly, data could be restored using:

$ btrfs-backup restore --snapshot-ext='bin'
                       --send-filter='/bin/dd if={file}'
                       --subvolume=subvolume/ backup/ snapshots/

[1] For the technically interested person: the reason the program
    appears stalled is because in order to provide reasonable error
    messages, btrfs-backup reads data from stderr. In the SSH example
    with ControlPersist set, when SSH is started and creates a new
    master connection it will fork a second instance into the background
    that keeps the master connection open. However, because it does not
    close stderr, btrfs-backup waits until the process terminates, i.e.,
    the master connection is shut down. For that matter, each SSH
    command issued exhibits a delay equal to the ControlPersist setting.
