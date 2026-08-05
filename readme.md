# DuoBreak

DuoBreak stores Duo Mobile credentials in a password-protected `.duo` vault and supports:

- **Duo Mobile Push** — normal push approval.
- **Verified Duo Push** — push approval requiring the code specified by Duo.
- **Duo Mobile Passcode** — counter-based passcodes.

## Step-by-Step Tutorial

### Initial Key Setup


1. Clone this repository and install the required Python packages:

    ```
    git clone https://github.com/JesseNaser/DuoBreak.git
    cd DuoBreak
    pip install -r requirements.txt
    ```

2. (for macOS only!) Install dependencies:

    ```
    brew install zbar
    sudo ln -s $(brew --prefix zbar)/lib/libzbar.dylib /usr/local/lib/libzbar.dylib
    ```

3. Run the `duobreak.py` script:

    ```
    python duobreak.py
    ```

4. Follow the on-screen instructions to create a new password-protected vault for storing your authentication keys.

5. On your computer, go to the Duo webpage and add a new device.

6. Save the QR code image given by the webpage as a PNG file.

7. In the DuoBreak script, choose "Add a key" from the main menu. Enter a nickname for the new key and provide the file path to the saved QR code image.

8. The script will automatically activate the new key and store it securely in your vault.

### Authentication

To authenticate, choose "Keys" from the main menu and select the key you want to use. You can choose to authenticate using Duo Push or Duo Passcodes.

## License

This project is licensed under the AGPL 3.0 or later license. Please see the [LICENSE](LICENSE) file for more information.