<div align="center">

# 🔐 PassManager Accounts
### Secure Password Manager with SHA-256 Hashing

![C](https://img.shields.io/badge/c-%2300599C.svg?style=for-the-badge&logo=c&logoColor=white)
![Security](https://img.shields.io/badge/Security-SHA--256-red?style=for-the-badge)
![Platform](https://img.shields.io/badge/Platform-Windows%20%7C%20Linux-lightgray?style=for-the-badge)

A lightweight, console-based password manager written entirely in C. It secures your account credentials locally using salted SHA-256 cryptographic hashing and a master password.

<img width="100" height="100" alt="Hadi Gholipour" src="https://github.com/user-attachments/assets/ae88fd88-e20c-46f5-9d29-9ea9e9618b26" style="border-radius: 50%; margin-top: 15px;" />

**[Follow me on LinkedIn](https://www.linkedin.com/in/hadi-gholipour-8717a1383)**

</div>

---

## 📸 Application Screenshots

<div align="center">
  <img width="800" alt="Screenshot 1" src="https://github.com/user-attachments/assets/b9e93586-cae0-46b8-a98f-9e62bb9f9430" />
  <br><br>
  <img width="800" alt="Screenshot 2" src="https://github.com/user-attachments/assets/7c013f2f-1fda-4575-bcc4-46a655e617f3" />
  <br><br>
  <img width="800" alt="Screenshot 3" src="https://github.com/user-attachments/assets/89276f8d-cd2c-4fa9-8a5c-abc82796fe3a" />
</div>

---

## ✨ Key Features

*   **🛡️ High Security:** Implements a custom SHA-256 hashing algorithm from scratch. Passwords are never stored in plain text.
*   **🧂 Cryptographic Salting:** Generates random 16-byte salts for every single entry to prevent rainbow table attacks.
*   **🔑 Master Password Protection:** The entire vault is locked behind a master password. You cannot read, write, or delete without verifying the master key.
*   **💾 Dynamic Local Storage:** Automatically saves and manages data locally using binary files (`master.dat` and `accounts.dat`).
*   **🛠️ Full CRUD Operations:** Easily Add, List, Search, and Delete your saved accounts.

---

## 🚀 How To Run

You have two ways to run this password manager:

### Option 1: Run the Executable (Windows)
If you already have the compiled `.exe` file:
1. Open your terminal or command prompt.
2. Run the executable:
   ```cmd
   passman.exe
   ```
   *(Note: The app will create `master.dat` and `accounts.dat` in the same folder to save your details.)*

### Option 2: Compile from Source (Windows/Linux/Mac)
If you want to compile the C code yourself, ensure you have a C compiler (like `gcc`) installed.

1. **Clone the repository:**
   ```bash
   git clone https://github.com/xedi1/PassManager-Accounts-With-Security-Hash-SHA256.git
   cd PassManager-Accounts-With-Security-Hash-SHA256
   ```
2. **Compile the code:**
   ```bash
   gcc src.c -o src
   ```
3. **Run the program:**
   ```bash
   ./src
   ```

---

## ⚙️ Under The Hood

This project demonstrates low-level memory and file management in C, alongside cryptographic principles:
*   **File I/O:** Uses `fread` and `fwrite` for reading/writing structured binary data to `.dat` files.
*   **Memory Management:** Utilizes dynamic memory allocation (`malloc`, `calloc`, `realloc`, `free`) to handle arbitrary lengths of account data safely.
*   **Bitwise Operations:** The SHA-256 implementation heavily relies on 32-bit and 64-bit bitwise shifts (`rotr`, `ch`, `maj`) to generate secure hashes.

---

<div align="center">
  <i>Developed with ❤️ by Hadi Gholipour. If you like this project, please give it a ⭐!</i>
</div>
```
