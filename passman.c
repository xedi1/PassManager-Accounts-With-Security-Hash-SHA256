
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

typedef uint8_t  u8;
typedef uint32_t u32;
typedef uint64_t u64;

static const u32 K256[64] = {
  0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
  0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
  0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
  0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
  0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
  0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
  0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
  0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

static u32 rotr(u32 x, unsigned n){ return (x >> n) | (x << (32-n)); }
static u32 ch(u32 x,u32 y,u32 z){ return (x & y) ^ (~x & z); }
static u32 maj(u32 x,u32 y,u32 z){ return (x & y) ^ (x & z) ^ (y & z); }
static u32 big_sigma0(u32 x){ return rotr(x,2) ^ rotr(x,13) ^ rotr(x,22); }
static u32 big_sigma1(u32 x){ return rotr(x,6) ^ rotr(x,11) ^ rotr(x,25); }
static u32 small_sigma0(u32 x){ return rotr(x,7) ^ rotr(x,18) ^ (x >> 3); }
static u32 small_sigma1(u32 x){ return rotr(x,17) ^ rotr(x,19) ^ (x >> 10); }

void sha256(const u8 *msg, size_t msglen, u8 out32[32]) {
    u64 bitlen = msglen * 8ULL;
    size_t newlen = msglen + 1;
    while (newlen % 64 != 56) newlen++;
    u8 *buf = calloc(newlen + 8, 1);
    if (!buf) return;
    memcpy(buf, msg, msglen);
    buf[msglen] = 0x80;
    // append length in bits big-endian
    for (int i = 0; i < 8; i++) buf[newlen + i] = (u8)(bitlen >> (56 - 8*i));

    // initial hash values
    u32 h0 = 0x6a09e667, h1 = 0xbb67ae85, h2 = 0x3c6ef372, h3 = 0xa54ff53a;
    u32 h4 = 0x510e527f, h5 = 0x9b05688c, h6 = 0x1f83d9ab, h7 = 0x5be0cd19;

    size_t chunks = (newlen + 8) / 64;
    for (size_t i = 0; i < chunks; ++i) {
        const u8 *chunk = buf + i*64;
        u32 w[64];
        for (int t = 0; t < 16; ++t) {
            w[t] = (u32)chunk[t*4] << 24 | (u32)chunk[t*4+1] << 16 | (u32)chunk[t*4+2] << 8 | (u32)chunk[t*4+3];
        }
        for (int t = 16; t < 64; ++t)
            w[t] = small_sigma1(w[t-2]) + w[t-7] + small_sigma0(w[t-15]) + w[t-16];

        u32 a = h0, b = h1, c = h2, d = h3, e = h4, f = h5, g = h6, hh = h7;
        for (int t = 0; t < 64; ++t) {
            u32 T1 = hh + big_sigma1(e) + ch(e,f,g) + K256[t] + w[t];
            u32 T2 = big_sigma0(a) + maj(a,b,c);
            hh = g; g = f; f = e; e = d + T1; d = c; c = b; b = a; a = T1 + T2;
        }
        h0 += a; h1 += b; h2 += c; h3 += d; h4 += e; h5 += f; h6 += g; h7 += hh;
    }
    free(buf);
    // write bytes big-endian
    u32 H[8] = {h0,h1,h2,h3,h4,h5,h6,h7};
    for (int i = 0; i < 8; ++i) {
        out32[i*4  ] = (u8)(H[i] >> 24);
        out32[i*4+1] = (u8)(H[i] >> 16);
        out32[i*4+2] = (u8)(H[i] >> 8);
        out32[i*4+3] = (u8)(H[i] >> 0);
    }
}

/* ------------ helpers: hex, salt, hashing wrapper -------------- */
void bytes_to_hex(const u8 *in, size_t inlen, char *out_hex /*size 2*inlen+1*/) {
    const char *hex = "0123456789abcdef";
    for (size_t i=0;i<inlen;i++){
        out_hex[i*2] = hex[(in[i] >> 4) & 0xF];
        out_hex[i*2+1] = hex[in[i] & 0xF];
    }
    out_hex[inlen*2] = '\0';
}

void rand_bytes(u8 *buf, size_t n) {
    for (size_t i=0;i<n;i++){
        buf[i] = (u8)(rand() & 0xFF);
    }
}

/* combine password+salt and produce hex sha256 */
void hash_password_hex(const char *password, const u8 *salt, size_t salt_len, char out_hex65[65]) {
    size_t plen = strlen(password);
    size_t tot = plen + salt_len;
    u8 *tmp = malloc(tot);
    if (!tmp) { out_hex65[0]=0; return; }
    memcpy(tmp, password, plen);
    memcpy(tmp+plen, salt, salt_len);
    u8 digest[32];
    sha256(tmp, tot, digest);
    bytes_to_hex(digest, 32, out_hex65);
    free(tmp);
}

/* ---------------- data structures ---------------- */
#define SERVICE_LEN 100
#define USER_LEN 100
#define HASH_HEX_LEN 65
#define SALT_LEN 16

typedef struct {
    char service[SERVICE_LEN];
    char username[USER_LEN];
    char password_hash[HASH_HEX_LEN]; // hex sha256 (64 chars + \0)
    u8 salt[SALT_LEN]; // raw salt bytes
} Account;

/* ---------------- file helpers ---------------- */
const char *MASTER_FILE = "master.dat";
const char *ACCT_FILE = "accounts.dat";

int master_exists() {
    FILE *f = fopen(MASTER_FILE, "rb");
    if (!f) return 0;
    fclose(f);
    return 1;
}

/* store master salt (16 bytes) followed by master hash (32 bytes) */
int save_master(const u8 *salt, const u8 *hash32) {
    FILE *f = fopen(MASTER_FILE, "wb");
    if (!f) return 0;
    if (fwrite(salt, 1, SALT_LEN, f) != SALT_LEN) { fclose(f); return 0; }
    if (fwrite(hash32, 1, 32, f) != 32) { fclose(f); return 0; }
    fclose(f);
    return 1;
}

int load_master(u8 *salt_out, u8 *hash32_out) {
    FILE *f = fopen(MASTER_FILE, "rb");
    if (!f) return 0;
    if (fread(salt_out, 1, SALT_LEN, f) != SALT_LEN) { fclose(f); return 0; }
    if (fread(hash32_out,1,32,f) != 32) { fclose(f); return 0; }
    fclose(f);
    return 1;
}

/* accounts file: write number of accounts (u32) then array of Account structs
   Note: salt stored raw, hash stored as hex string */
int save_accounts(Account *arr, size_t n) {
    FILE *f = fopen(ACCT_FILE, "wb");
    if (!f) return 0;
    u32 nn = (u32)n;
    if (fwrite(&nn, sizeof(nn), 1, f) != 1) { fclose(f); return 0; }
    for (size_t i=0;i<n;i++){
        if (fwrite(&arr[i], sizeof(Account), 1, f) != 1) { fclose(f); return 0; }
    }
    fclose(f);
    return 1;
}

Account *load_accounts(size_t *out_n) {
    *out_n = 0;
    FILE *f = fopen(ACCT_FILE, "rb");
    if (!f) return NULL;
    u32 nn;
    if (fread(&nn, sizeof(nn), 1, f) != 1) { fclose(f); return NULL; }
    Account *arr = malloc((size_t)nn * sizeof(Account));
    if (!arr) { fclose(f); return NULL; }
    for (u32 i=0;i<nn;i++){
        if (fread(&arr[i], sizeof(Account), 1, f) != 1) { free(arr); fclose(f); return NULL; }
    }
    fclose(f);
    *out_n = nn;
    return arr;
}

/* ---------------- core functionality ---------------- */

int set_master_password_interactive() {
    char pass1[256], pass2[256];
    printf("Set master password: ");
    if (!fgets(pass1, sizeof(pass1), stdin)) return 0;
    pass1[strcspn(pass1,"\n")] = 0;
    if (strlen(pass1) == 0) { printf("Empty password not allowed.\n"); return 0; }
    printf("Repeat master password: ");
    if (!fgets(pass2, sizeof(pass2), stdin)) return 0;
    pass2[strcspn(pass2,"\n")] = 0;
    if (strcmp(pass1, pass2) != 0) { printf("Passwords do not match.\n"); return 0; }

    u8 salt[SALT_LEN];
    rand_bytes(salt, SALT_LEN);
    u8 digest[32];
    // compute raw digest of pass+salt
    size_t plen = strlen(pass1);
    u8 *tmp = malloc(plen + SALT_LEN);
    if (!tmp) return 0;
    memcpy(tmp, pass1, plen); memcpy(tmp+plen, salt, SALT_LEN);
    sha256(tmp, plen + SALT_LEN, digest);
    free(tmp);
    if (!save_master(salt, digest)) { printf("Failed to save master.\n"); return 0; }
    printf("Master password set and saved.\n");
    return 1;
}

int verify_master_interactive() {
    if (!master_exists()) {
        printf("No master found. You must set a master password first.\n");
        return 0;
    }
    u8 salt[SALT_LEN], stored_digest[32];
    if (!load_master(salt, stored_digest)) { printf("Failed to load master.\n"); return 0; }
    char pass[256];
    printf("Enter master password: ");
    if (!fgets(pass, sizeof(pass), stdin)) return 0;
    pass[strcspn(pass,"\n")] = 0;
    size_t plen = strlen(pass);
    u8 *tmp = malloc(plen + SALT_LEN); if (!tmp) return 0;
    memcpy(tmp, pass, plen); memcpy(tmp+plen, salt, SALT_LEN);
    u8 digest[32]; sha256(tmp, plen + SALT_LEN, digest);
    free(tmp);
    if (memcmp(digest, stored_digest, 32) == 0) return 1;
    return 0;
}

void add_account_interactive() {
    size_t n = 0;
    Account *arr = load_accounts(&n);
    // we'll append one
    Account acc;
    memset(&acc, 0, sizeof(acc));
    printf("Service name (e.g. Gmail): ");
    if (!fgets(acc.service, sizeof(acc.service), stdin)) return;
    acc.service[strcspn(acc.service,"\n")] = 0;
    printf("Username: ");
    if (!fgets(acc.username, sizeof(acc.username), stdin)) return;
    acc.username[strcspn(acc.username,"\n")] = 0;
    char pass[256];
    printf("Password: ");
    if (!fgets(pass, sizeof(pass), stdin)) return;
    pass[strcspn(pass,"\n")] = 0;

    // salt
    rand_bytes(acc.salt, SALT_LEN);
    // hash pass+salt to hex
    hash_password_hex(pass, acc.salt, SALT_LEN, acc.password_hash);

    // append
    Account *newarr = realloc(arr, (n+1)*sizeof(Account));
    if (!newarr) { free(arr); printf("Memory error\n"); return; }
    newarr[n] = acc;
    if (!save_accounts(newarr, n+1)) { printf("Failed to save accounts\n"); free(newarr); return; }
    printf("Account saved.\n");
    free(newarr);
}

void list_accounts_interactive() {
    size_t n=0;
    Account *arr = load_accounts(&n);
    if (!arr) { printf("No accounts stored.\n"); return; }
    printf("Stored accounts (%zu):\n", n);
    for (size_t i=0;i<n;i++){
        printf("[%zu] Service: %s | User: %s | PassHash: %s\n", i+1, arr[i].service, arr[i].username, arr[i].password_hash);
    }
    free(arr);
}

/* show account with option to reveal password? we don't store raw password, only hash */
void search_account_interactive() {
    char key[100];
    printf("Enter service name to search: ");
    if (!fgets(key, sizeof(key), stdin)) return;
    key[strcspn(key,"\n")] = 0;
    size_t n=0; Account *arr = load_accounts(&n);
    if (!arr) { printf("No accounts.\n"); return; }
    int found=0;
    for (size_t i=0;i<n;i++){
        if (strcasecmp(arr[i].service, key) == 0) {
            printf("Found: Service: %s | User: %s | PassHash: %s\n", arr[i].service, arr[i].username, arr[i].password_hash);
            found = 1;
        }
    }
    if (!found) printf("Not found.\n");
    free(arr);
}

void delete_account_interactive() {
    size_t n=0; Account *arr = load_accounts(&n);
    if (!arr) { printf("No accounts.\n"); return; }
    printf("Enter service name to delete: ");
    char key[100]; if (!fgets(key,sizeof(key),stdin)) { free(arr); return; }
    key[strcspn(key,"\n")] = 0;
    size_t write_idx=0;
    int deleted=0;
    for (size_t i=0;i<n;i++){
        if (strcasecmp(arr[i].service, key) == 0) {
            deleted = 1;
            continue; // skip copying this one
        }
        arr[write_idx++] = arr[i];
    }
    if (!deleted) { printf("Service not found.\n"); free(arr); return; }
    if (!save_accounts(arr, write_idx)) { printf("Error saving file after deletion.\n"); }
    else printf("Deleted %s (if existed)\n", key);
    free(arr);
}

void change_master_interactive() {
    // verify first
    if (!verify_master_interactive()) { printf("Master password incorrect. Cannot change.\n"); return; }
    // set new
    char new1[256], new2[256];
    printf("New master password: "); if (!fgets(new1,sizeof(new1),stdin)) return; new1[strcspn(new1,"\n")]=0;
    printf("Repeat new master: "); if (!fgets(new2,sizeof(new2),stdin)) return; new2[strcspn(new2,"\n")]=0;
    if (strcmp(new1,new2) != 0) { printf("Do not match.\n"); return; }
    u8 salt[SALT_LEN], digest[32];
    rand_bytes(salt, SALT_LEN);
    size_t plen = strlen(new1);
    u8 *tmp = malloc(plen + SALT_LEN); if (!tmp) return;
    memcpy(tmp, new1, plen); memcpy(tmp+plen, salt, SALT_LEN);
    sha256(tmp, plen + SALT_LEN, digest);
    free(tmp);
    if (!save_master(salt, digest)) { printf("Save failed.\n"); return; }
    printf("Master changed.\n");
}

/* ---------------- UI ---------------- */
void show_menu() {
    printf("\n===== PASSMAN MENU =====\n");
    printf("1) Set master password (only if none set)\n");
    printf("2) Verify master and enter\n");
    printf("3) Add account\n");
    printf("4) List accounts\n");
    printf("5) Search account\n");
    printf("6) Delete account\n");
    printf("7) Change master password\n");
    printf("8) Exit\n");
    printf("Choice: ");
}

int main(void) {
    srand((unsigned)time(NULL));
    char line[16];
    while (1) {
        show_menu();
        if (!fgets(line, sizeof(line), stdin)) break;
        int choice = atoi(line);
        if (choice == 1) {
            if (master_exists()) { printf("Master already exists.\n"); continue; }
            set_master_password_interactive();
        } else if (choice == 2) {
            if (verify_master_interactive()) printf("Master OK. You may use other functions.\n");
            else printf("Master incorrect.\n");
        } else if (choice == 3) {
            if (!verify_master_interactive()) { printf("Master verification failed. Cannot add.\n"); continue; }
            add_account_interactive();
        } else if (choice == 4) {
            if (!verify_master_interactive()) { printf("Master verification failed. Cannot list.\n"); continue; }
            list_accounts_interactive();
        } else if (choice == 5) {
            if (!verify_master_interactive()) { printf("Master verification failed. Cannot search.\n"); continue; }
            search_account_interactive();
        } else if (choice == 6) {
            if (!verify_master_interactive()) { printf("Master verification failed. Cannot delete.\n"); continue; }
            delete_account_interactive();
        } else if (choice == 7) {
            change_master_interactive();
        } else if (choice == 8) {
            printf("Bye.\n"); break;
        } else {
            printf("Invalid choice.\n");
        }
    }
    return 0;
}