#!/usr/bin/env bash

set -euo pipefail

readonly source_branch="ss"
readonly target_branch="main"
readonly -a excluded_paths=(
  "AGENTS.md"
  "note"
  "data"
)

die() {
  printf 'error: %s\n' "$*" >&2
  exit 1
}

repo_root="$(git rev-parse --show-toplevel 2>/dev/null)" ||
  die "Git リポジトリ内で実行してください。"
cd "$repo_root"

git show-ref --verify --quiet "refs/heads/${source_branch}" ||
  die "ローカルブランチ '${source_branch}' が見つかりません。"
git show-ref --verify --quiet "refs/heads/${target_branch}" ||
  die "ローカルブランチ '${target_branch}' が見つかりません。"

if [[ -n "$(git status --porcelain --untracked-files=all)" ]]; then
  die "未コミットの変更があります。commit または stash してから再実行してください。"
fi

git switch "$target_branch"
target_before_merge="$(git rev-parse HEAD)"

if git merge-base --is-ancestor "$source_branch" "$target_branch"; then
  printf "'%s' はすでに '%s' にマージされています。\n" \
    "$source_branch" "$target_branch"
  exit 0
fi

merge_status=0
git merge --no-ff --no-commit "$source_branch" || merge_status=$?

if ! git rev-parse --quiet --verify MERGE_HEAD >/dev/null; then
  die "マージを開始できませんでした (git merge の終了コード: ${merge_status})。"
fi

# 除外対象を、マージ開始直前の main と同じ状態に戻す。
# ss にだけ存在するファイルは削除され、main に存在するファイルは保持される。
for excluded_path in "${excluded_paths[@]}"; do
  if git cat-file -e "${target_before_merge}:${excluded_path}" 2>/dev/null ||
    git ls-files --error-unmatch -- "$excluded_path" >/dev/null 2>&1; then
    git restore \
      --source="$target_before_merge" \
      --staged \
      --worktree \
      -- "$excluded_path"
  fi
done

unmerged_paths="$(git diff --name-only --diff-filter=U)"
if [[ -n "$unmerged_paths" ]]; then
  printf '%s\n' \
    "除外対象以外に競合があります。" \
    "競合を解決した後、git commit でマージを完了してください。" \
    "マージを取り消す場合は git merge --abort を実行してください。" >&2
  printf '\n競合ファイル:\n%s\n' "$unmerged_paths" >&2
  exit 1
fi

git commit --no-edit

printf "'%s' から '%s' へのマージが完了しました。\n" \
  "$source_branch" "$target_branch"
printf '除外: %s\n' "${excluded_paths[*]}"
