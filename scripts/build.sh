#!/bin/bash
#
# OTLP Go SDK - Build Script
# Cross-platform build script for Windows (Git Bash/WSL), Linux, and macOS
#

set -e

# Colors for output
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" || "$OS" == "Windows_NT" ]]; then
    CYAN=""
    GREEN=""
    YELLOW=""
    RED=""
    RESET=""
else
    CYAN='\033[36m'
    GREEN='\033[32m'
    YELLOW='\033[33m'
    RED='\033[31m'
    RESET='\033[0m'
fi

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

# Configuration
PROJECT_NAME="otlp-go"
BUILD_DIR="${PROJECT_ROOT}/build"
BIN_DIR="${PROJECT_ROOT}/bin"
RELEASE_DIR="${BUILD_DIR}/release"

# Build configuration
VERSION=$(git describe --tags --always --dirty 2>/dev/null || echo "dev")
BUILD_TIME=$(date -u +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || echo "unknown")
GIT_COMMIT=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
LDFLAGS="-X main.Version=${VERSION} -X main.BuildTime=${BUILD_TIME} -X main.GitCommit=${GIT_COMMIT}"

# Build options
BUILD_TYPE="debug"
TARGET_OS=""
TARGET_ARCH=""
CLEAN_BUILD=false
SKIP_TESTS=false
BUILD_EXAMPLES=false
PARALLEL=false

# Supported platforms
PLATFORMS=("linux/amd64" "linux/arm64" "darwin/amd64" "darwin/arm64" "windows/amd64")

# Functions
print_header() {
    echo -e "${CYAN}========================================${RESET}"
    echo -e "${CYAN}$1${RESET}"
    echo -e "${CYAN}========================================${RESET}"
}

print_success() {
    echo -e "${GREEN}✅ $1${RESET}"
}

print_warning() {
    echo -e "${YELLOW}⚠️  $1${RESET}"
}

print_error() {
    echo -e "${RED}❌ $1${RESET}"
}

print_info() {
    echo -e "${CYAN}ℹ️  $1${RESET}"
}

show_help() {
    cat << EOF
OTLP Go SDK Build Script

Usage: $0 [OPTIONS]

Options:
    -h, --help              Show this help message
    -t, --type TYPE         Build type: debug|release (default: debug)
    -o, --os OS             Target OS (linux|darwin|windows)
    -a, --arch ARCH         Target architecture (amd64|arm64)
    -c, --clean             Clean build (remove build directory first)
    -s, --skip-tests        Skip running tests
    -e, --examples          Build example binaries
    -r, --release           Build release for all platforms
    -p, --parallel          Build in parallel (requires background job support)
    -v, --verbose           Verbose output

Examples:
    $0                      Build debug version
    $0 -t release           Build release version
    $0 -o linux -a amd64    Build for Linux AMD64
    $0 -c -t release        Clean build release version
    $0 -r                   Build release for all platforms
    $0 -e                   Build with example binaries
EOF
}

parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -t|--type)
                BUILD_TYPE="$2"
                shift 2
                ;;
            -o|--os)
                TARGET_OS="$2"
                shift 2
                ;;
            -a|--arch)
                TARGET_ARCH="$2"
                shift 2
                ;;
            -c|--clean)
                CLEAN_BUILD=true
                shift
                ;;
            -s|--skip-tests)
                SKIP_TESTS=true
                shift
                ;;
            -e|--examples)
                BUILD_EXAMPLES=true
                shift
                ;;
            -r|--release)
                BUILD_TYPE="release"
                shift
                ;;
            -p|--parallel)
                PARALLEL=true
                shift
                ;;
            -v|--verbose)
                set -x
                shift
                ;;
            *)
                print_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done
}

setup() {
    print_header "OTLP Go SDK - Build Script"
    
    # Check Go installation
    if ! command -v go &> /dev/null; then
        print_error "Go is not installed or not in PATH"
        exit 1
    fi
    
    GO_VERSION=$(go version | awk '{print $3}')
    print_info "Go version: ${GO_VERSION}"
    print_info "Project: ${PROJECT_NAME}"
    print_info "Version: ${VERSION}"
    print_info "Build time: ${BUILD_TIME}"
    print_info "Git commit: ${GIT_COMMIT}"
    
    # Clean build if requested
    if [[ "$CLEAN_BUILD" == true ]]; then
        print_info "Cleaning build directory..."
        rm -rf "${BUILD_DIR}"
        rm -rf "${BIN_DIR}"
    fi
    
    # Create directories
    mkdir -p "${BUILD_DIR}"
    mkdir -p "${BIN_DIR}"
    mkdir -p "${RELEASE_DIR}"
    
    # Change to project root
    cd "${PROJECT_ROOT}"
    
    # Sync workspace
    print_info "Syncing workspace..."
    go work sync
}

run_tests() {
    if [[ "$SKIP_TESTS" == false ]]; then
        print_header "Running Tests"
        if go test -race -short ./...; then
            print_success "Tests passed"
        else
            print_error "Tests failed"
            exit 1
        fi
    else
        print_warning "Skipping tests"
    fi
}

build_module() {
    local module_path="$1"
    local output_name="$2"
    local goos="$3"
    local goarch="$4"
    
    local build_flags=()
    local output_path="${BIN_DIR}/${output_name}"
    
    if [[ -n "$goos" ]]; then
        export GOOS="$goos"
        export GOARCH="$goarch"
        output_path="${RELEASE_DIR}/${output_name}"
    fi
    
    if [[ "$BUILD_TYPE" == "release" ]]; then
        build_flags+=("-ldflags" "-s -w ${LDFLAGS}")
    else
        build_flags+=("-ldflags" "${LDFLAGS}")
    fi
    
    print_info "Building: ${module_path} -> ${output_path}"
    
    if go build "${build_flags[@]}" -o "${output_path}" "${module_path}"; then
        print_success "Built: ${output_name}"
    else
        print_error "Failed to build: ${output_name}"
        return 1
    fi
    
    # Reset environment
    unset GOOS
    unset GOARCH
}

build_all() {
    print_header "Building Modules"
    
    # Determine build targets
    local build_targets=()
    
    if [[ -n "$TARGET_OS" && -n "$TARGET_ARCH" ]]; then
        # Single platform build
        build_targets=("${TARGET_OS}/${TARGET_ARCH}")
    elif [[ "$BUILD_TYPE" == "release" ]]; then
        # Release build for all platforms
        build_targets=("${PLATFORMS[@]}")
    else
        # Local build (current platform)
        local current_os
        local current_arch
        current_os=$(go env GOOS)
        current_arch=$(go env GOARCH)
        build_targets=("${current_os}/${current_arch}")
    fi
    
    local failed=0
    
    for platform in "${build_targets[@]}"; do
        local goos="${platform%/*}"
        local goarch="${platform#*/}"
        local ext=""
        
        if [[ "$goos" == "windows" ]]; then
            ext=".exe"
        fi
        
        print_info "Building for ${goos}/${goarch}..."
        
        # Build main modules
        if ! build_module "." "${PROJECT_NAME}-${goos}-${goarch}${ext}" "$goos" "$goarch"; then
            failed=$((failed + 1))
        fi
        
        # Build examples if requested
        if [[ "$BUILD_EXAMPLES" == true ]]; then
            build_examples "$goos" "$goarch" "$ext"
        fi
    done
    
    if [[ $failed -gt 0 ]]; then
        print_error "${failed} build(s) failed"
        exit 1
    fi
}

build_examples() {
    local goos="$1"
    local goarch="$2"
    local ext="$3"
    
    print_info "Building examples for ${goos}/${goarch}..."
    
    for example_dir in examples/*/; do
        if [[ -f "${example_dir}main.go" ]]; then
            local example_name
            example_name=$(basename "$example_dir")
            local output_name="example-${example_name}-${goos}-${goarch}${ext}"
            
            build_module "${example_dir}" "${output_name}" "$goos" "$goarch" || true
        fi
    done
}

verify_build() {
    print_header "Verifying Build"
    
    local binaries
    binaries=$(find "${BIN_DIR}" -type f -executable 2>/dev/null || find "${BIN_DIR}" -type f 2>/dev/null)
    
    if [[ -z "$binaries" ]]; then
        print_warning "No binaries found in ${BIN_DIR}"
    else
        print_info "Built binaries:"
        echo "$binaries" | while read -r binary; do
            local size
            size=$(du -h "$binary" 2>/dev/null | cut -f1 || echo "unknown")
            echo "  - $(basename "$binary") (${size})"
        done
    fi
    
    # Check Go module consistency
    print_info "Verifying Go modules..."
    if go mod verify; then
        print_success "Module verification passed"
    else
        print_warning "Module verification had issues"
    fi
}

generate_checksums() {
    if [[ "$BUILD_TYPE" == "release" ]]; then
        print_header "Generating Checksums"
        
        cd "${RELEASE_DIR}"
        
        # Generate SHA256 checksums
        if command -v sha256sum &> /dev/null; then
            sha256sum * > checksums-sha256.txt
            print_success "SHA256 checksums generated"
        elif command -v shasum &> /dev/null; then
            shasum -a 256 * > checksums-sha256.txt
            print_success "SHA256 checksums generated"
        else
            print_warning "Checksum utility not found"
        fi
        
        cd - > /dev/null
    fi
}

print_summary() {
    print_header "Build Summary"
    
    print_info "Build type: ${BUILD_TYPE}"
    print_info "Version: ${VERSION}"
    print_info "Output directory: ${BIN_DIR}"
    
    if [[ "$BUILD_TYPE" == "release" ]]; then
        print_info "Release directory: ${RELEASE_DIR}"
    fi
    
    # Count binaries
    local binary_count
    binary_count=$(find "${BIN_DIR}" -type f 2>/dev/null | wc -l)
    print_info "Built binaries: ${binary_count}"
    
    print_success "Build completed successfully!"
}

main() {
    parse_args "$@"
    setup
    run_tests
    build_all
    verify_build
    generate_checksums
    print_summary
}

# Run main function
trap 'print_error "Build interrupted"; exit 1' INT TERM
main "$@"
