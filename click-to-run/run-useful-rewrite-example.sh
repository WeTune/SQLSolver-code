app="useful_rewrite_example"
tag="base"
target="${app}"

while [[ $# -gt 0 ]]; do
  case "$1" in
  "-tag")
    tag="${2}"
    shift 2
    ;;
  *)
    positional_args+=("${1}")
    shift
    ;;
  esac
done

mkdir -p wtune_data/profile/WeTune/past
mv wtune_data/profile/WeTune/${tag}_WeTune_ss.*.csv wtune_data/profile/WeTune/past

click-to-run/make-db.sh -tag "${tag}" -app "${app}"
click-to-run/generate-data.sh -tag "${tag}" -app "${app}" -target "${target}"

click-to-run/profile-cost.sh -app "${app}" -tag "${tag}"
echo "Result details are in wtune_data/profile/WeTune/${tag}_WeTune_ss.<TIME>.csv"
echo "                   or wtune_data/profile/WeTune/past/${tag}_WeTune_ss.<TIME>.csv"
