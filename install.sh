#!/bin/sh

USER=smfs
GROUP=smfs
DIR=/var/spool/smfs
UNAME=`uname`
PATH=$PATH:/sbin:/bin:/usr/sbin:/usr/bin

export PATH

echo -n "Creating the required user ($USER) and group ($GROUP)... "
if grep "^$GROUP:" /etc/group > /dev/null ; then
    :
else
    case $UNAME in
	*BSD)
	    pw groupadd -n $GROUP
	    ;;
	*)
	    groupadd $GROUP
    esac
fi
if grep "^$USER:" /etc/passwd > /dev/null ; then
    :
else
    case $UNAME in
	*BSD)
	    pw useradd -g $GROUP -n $USER -d /dev/null -s /dev/null
	    ;;
	*)
	    useradd -g $GROUP $USER -d /dev/null -s /dev/null
    esac
fi
echo "done."
if [ ! -d $DIR ]; then
	echo -n "Creating /var/spool/smfs..."
	mkdir $DIR
	chown $USER $DIR
	chgrp $GROUP $DIR
	chmod 700 $DIR
	echo "done."
fi
