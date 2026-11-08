# LeanHash 開発環境の共通設定。actions と対話シェルの両方から source する。
# 各 SDK の setup-project フックがユーザーのホーム配下にツールを入れる前提。
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$HOME/.local/bin:$PATH"
export LEANHASH_TOOLS="$HOME/.local/opt"
if [ -d "$HOME/.opam" ] && command -v opam >/dev/null 2>&1; then
  eval "$(opam env --switch=5.3.0 --set-switch 2>/dev/null || true)"
fi
