# How to Run the Verification Suite

This document provides detailed instructions for running the TLA+ model checker and the Python simulator.

### **Option 1: The Easy Way (Recommended)**

This method uses Docker to create a perfectly configured environment and runs the entire verification suite with just two commands. It is the most reliable way to reproduce our results.

**Prerequisites:**
*   [Docker Desktop](https://www.docker.com/products/docker-desktop/) installed and running.

**Instructions:**
1.  Open a terminal or command prompt and navigate to the root directory of this project (`alpenglow-formal-verification`).
2.  **First, build the Docker image.** This command reads the `tools/Dockerfile`, builds the verification environment, and names it `alpenglow-verify`. This may take a few minutes on the first run.
    ```bash
    docker build -t alpenglow-verify -f tools/Dockerfile .
    ```
3.  **After the build is complete, run the verification.** This command starts a container from the image you just built, which automatically runs both the TLA+ check and the Python simulation. It maps the container's `results` folder to your local `results` folder so you can see the output.
    ```bash
    docker run --rm -v "%cd%/results:/app/results" alpenglow-verify
    ```

After the run is complete, all output and data files will be saved in the `results/` directory on your local machine.

---

### **Option 2: Running Components Manually (Without Docker)**

If you prefer not to use Docker, you can run the tools manually by installing the dependencies on your system.

#### **Running the TLA+ Model Checker**

**Prerequisites:**
*   Java 17+
*   The `tla2tools.jar` file, which can be downloaded from the [TLA+ GitHub releases page](https://github.com/tlaplus/tlaplus/releases).

**Instructions:**
1.  Download `tla2tools.jar` and place it in a known location.
2.  From the project's root directory, run the following command, replacing `/path/to/your/` with the actual path:
    ```bash
    java -jar /path/to/your/tla2tools.jar -config specs/tla/Alpenglow.cfg specs/tla/Alpenglow.tla
    ```
This will run an exhaustive check on the small 4-node configuration. TLC will report if it finds any invariant violations or when it finishes successfully.

#### **Running the Python Simulator**

**Prerequisites:**
*   Python 3.8+

**Instructions:**
1.  Navigate to the project's root directory in your terminal.
2.  Install the required Python packages:
    ```bash
    pip install -r sim/requirements.txt
    ```
3.  Run the simulator with the default "20+20" configuration:
    
This will produce `.csv` files in the `results/` directory with detailed statistics from the simulation.

