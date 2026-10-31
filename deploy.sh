#!/bin/bash
# Überträgt das Dashboard auf den Pi. Daten (.*.json, todos.json), .env und node_modules bleiben auf dem Pi unberührt.
cd "$(dirname "$0")" || exit 1
rsync -av --delete \
  --exclude='.git/' --exclude='node_modules/' --exclude='.env' \
  --exclude='.DS_Store' --exclude='.*.json' --exclude='todos.json' --exclude='deploy.sh' \
  ./ chris@192.168.178.133:/home/chris/www/ || exit 1
ssh chris@192.168.178.133 'bash -ic "cd ~/www && pm2 restart mein-dashboard"'
