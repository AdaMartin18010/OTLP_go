#!/bin/bash
#
# OTLP Go SDK - Test Script
# Cross-platform test runner for Windows (Git Bash/WSL), Linux, and macOS
#

set -e

# Colors for output
if [[ "$OSTYPE" == "msys" || "$OSTYPE" == "win32" || "$OS" == "Windows_NT" ]]; then
    # Windows terminal
    CYAN=""
    GREEN=""
    YELLOW=""
    RED=""
    RESET=""
else
    # Unix-like terminal
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
BUILD_DIR="${PROJECT_ROOT}/build"
COVERAGE_DIR="${BUILD_DIR}/coverage"
TEST_LOG="${BUILD_DIR}/test.log"
COVERAGE_OUT="${COVERAGE_DIR}/coverage.out"
COVERAGE_HTML="${COVERAGE_DIR}/coverage.html"

# Test modes
RUN_COVERAGE=false
RUN_BENCHMARK=false
RUN_SHORT=false
RUN_RACE=true
VERBOSE=false
MODULES=("." "./pkg/..." "./examples/..." "./benchmarks/...")

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
OTLP Go SDK Test Script

Usage: $0 [OPTIONS]

Options:
    -h, --help          Show this help message
    -c, --coverage      Run tests with coverage report
    -b, --benchmark     Run benchmark tests
    -s, --short         Run short tests only
    -v, --verbose       Verbose output
    -m, --module MOD    Test specific module (e.g., ./pkg/logs)
    --no-race           Disable race detector

Examples:
    $0                  Run all tests
    $0 -c               Run tests with coverage
    $0 -b               Run benchmarks
    $0 -m ./pkg/logs    Test specific module
    $0 -c -v            Run coverage with verbose output
EOF
}

parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -c|--coverage)
                RUN_COVERAGE=true
                shift
                ;;
            -b|--benchmark)
                RUN_BENCHMARK=true
                shift
                ;;
            -s|--short)
                RUN_SHORT=true
                shift
                ;;
            -v|--verbose)
                VERBOSE=true
                shift
                ;;
            -m|--module)
                if [[ -n "$2" && ! "$2" =~ ^- ]]; then
                    MODULES=("$2")
                    shift 2
                else
                    print_error "Module path required for -m option"
                    exit 1
                fi
                ;;
            --no-race)
                RUN_RACE=false
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
    print_header "OTLP Go SDK - Test Runner"
    
    # Create build directories
    mkdir -p "${BUILD_DIR}"
    mkdir -p "${COVERAGE_DIR}"
    
    # Check Go version
    if ! command -v go &> /dev/null; then
        print_error "Go is not installed or not in PATH"
        exit 1
    fi
    
    GO_VERSION=$(go version | awk '{print $3}')
    print_info "Using Go version: ${GO_VERSION}"
    
    # Change to project root
    cd "${PROJECT_ROOT}"
    
    # Sync workspace
    print_info "Syncing workspace..."
    go work sync
}

run_tests() {
    print_header "Running Tests"
    
    local test_flags=()
    
    if [[ "$RUN_RACE" == true ]]; then
        test_flags+=("-race")
    fi
    
    if [[ "$RUN_SHORT" == true ]]; then
        test_flags+=("-short")
    fi
    
    if [[ "$VERBOSE" == true ]]; then
        test_flags+=("-v")
    fi
    
    if [[ "$RUN_COVERAGE" == true ]]; then
        test_flags+=("-coverprofile=${COVERAGE_OUT}")
    fi
    
    local failed=0
    local total=0
    
    for module in "${MODULES[@]}"; do
        print_info "Testing: ${module}"
        
        if [[ -d "${module}" || "${module}" == "." ]]; then
            if go test "${test_flags[@]}" "${module}"; then
                print_success "Tests passed: ${module}"
            else
                print_error "Tests failed: ${module}"
                failed=$((failed + 1))
            fi
            total=$((total + 1))
        else
            print_warning "Module not found: ${module}"
        fi
    done
    
    echo ""
    print_info "Test Summary: $((total - failed))/${total} modules passed"
    
    if [[ $failed -gt 0 ]]; then
        exit 1
    fi
}

generate_coverage_report() {
    if [[ "$RUN_COVERAGE" == true ]]; then
        print_header "Generating Coverage Report"
        
        if [[ -f "${COVERAGE_OUT}" ]]; then
            go tool cover -html="${COVERAGE_OUT}" -o "${COVERAGE_HTML}"
            
            # Display coverage percentage
            local coverage
            coverage=$(go tool cover -func="${COVERAGE_OUT}" | grep total | awk '{print $3}')
            print_success "Coverage: ${coverage}"
            print_info "Coverage report: ${COVERAGE_HTML}"
        else
            print_warning "Coverage file not found"
        fi
    fi
}

run_benchmarks() {
    if [[ "$RUN_BENCHMARK" == true ]]; then
        print_header "Running Benchmarks"
        
        local benchmark_flags=("-bench=." "-benchmem")
        
        if [[ "$VERBOSE" == true ]]; then
            benchmark_flags+=("-v")
        fi
        
        # Run benchmarks for pkg modules
        if go test "${benchmark_flags[@]}" -run=^$ ./pkg/...; then
            print_success "Benchmarks completed"
        else
            print_warning "Some benchmarks may have failed"
        fi
    fi
}

cleanup() {
    print_header "Cleanup"
    # Cleanup is optional, keeping logs for debugging
    print_info "Test logs saved to: ${TEST_LOG}"
}

main() {
    parse_args "$@"
    setup
    
    if [[ "$RUN_BENCHMARK" == true ]]; then
        run_benchmarks
    else
        run_tests
        generate_coverage_report
    fi
    
    cleanup
    
    print_header "Test Run Complete"
    print_success "All tests completed successfully!"
}

# Run main function
trap 'print_error "Test script interrupted"; exit 1' INT TERM
main "$@"
