FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1

RUN apt-get update && apt-get install -y \
    chromium chromium-driver \
    fonts-liberation libnss3 libxss1 libasound2 \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY . .
ENV PORT=10000 CHROME_BIN=/usr/bin/chromium
CMD ["python","LeverageLensServer_1.92_linux.py"]

