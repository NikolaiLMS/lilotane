while [[ "$#" -gt 0 ]]; do
    case $1 in
        -e|--engine) engine_dir="$2"; shift ;;
        -p|--parser) uglify=1 ;;
        *) echo "Unknown parameter passed: $1"; exit 1 ;;
    esac
    shift
done

eval $
