# Dockerfile for Alpenglow Formal Verification
# This creates a reproducible environment with all necessary tools.

# Use a base image with Java for TLA+
FROM eclipse-temurin:17-jdk-jammy

# Install Python and other utilities
RUN apt-get update && apt-get install -y \
    python3 \
    python3-pip \
    python3-venv \
    unzip \
    wget \
    && rm -rf /var/lib/apt/lists/*

# CORRECTED STEP: Set up the working directory FIRST.
# This creates the /app folder.
WORKDIR /app

# Download TLA+ tools directly into the /app directory
ENV TLA_VERSION=1.8.0
ENV TLA_JAR=/app/tla2tools.jar
RUN wget https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar -O ${TLA_JAR}

# Copy the project files into the /app directory
COPY . .

# Install Python dependencies
RUN python3 -m venv venv
RUN . venv/bin/activate && pip install -r sim/requirements.txt

# Set the entrypoint to run the full verification suite
ENTRYPOINT ["make", "verify-all"]

