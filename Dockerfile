# hebelwatch-server/Dockerfile
FROM python:3.11-slim
WORKDIR /app

# System-Dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    chromium chromium-driver \
    libglib2.0-0 libnss3 libgdk-pixbuf2.0-0 libgtk-3-0 \
    fonts-liberation ca-certificates \
 && rm -rf /var/lib/apt/lists/*

RUN python -m pip install --upgrade pip

COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY . /app

# Startet deine Dash/Flask-App
CMD ["python", "LeverageLens.py"]
# (oder: CMD ["gunicorn","LeverageLens:server","--bind","0.0.0.0:8050"])

