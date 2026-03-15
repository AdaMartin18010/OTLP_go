#!/bin/bash
#
# OTLP Go SDK - Lint Script
# Cross-platform code linting and quality checks for Windows, Linux, and macOS
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
BUILD_DIR="${PROJECT_ROOT}/build"
LINT_DIR="${BUILD_DIR}/lint"
LINT_LOG="${LINT_DIR}/lint.log"

# Lint options
RUN_GOFMT=true
RUN_GOVET=true
RUN_GOLANGCI_LINT=true
RUN_STATICCHECK=true
RUN_VULNCHECK=false
FIX_ISSUES=false
VERBOSE=false
MODULES=("." "./pkg/..." "./examples/...")

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
OTLP Go SDK Lint Script

Usage: $0 [OPTIONS]

Options:
    -h, --help              Show this help message
    -f, --fix               Auto-fix issues where possible
    -v, --verbose           Verbose output
    --no-fmt                Skip gofmt check
    --no-vet                Skip go vet
    --no-golangci           Skip golangci-lint
    --no-staticcheck        Skip staticcheck
    --vulncheck             Run vulnerability check
    -m, --module MOD        Lint specific module only

Examples:
    $0                      Run all linters
    $0 -f                   Run linters and auto-fix
    $0 --vulncheck          Include vulnerability check
    $0 -m ./pkg/logs        Lint specific module
EOF
}

parse_args() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -f|--fix)
                FIX_ISSUES=true
                shift
                ;;
            -v|--verbose)
                VERBOSE=true
                shift
                ;;
            --no-fmt)
                RUN_GOFMT=false
                shift
                ;;
            --no-vet)
                RUN_GOVET=false
                shift
                ;;
            --no-golangci)
                RUN_GOLANGCI_LINT=false
                shift
                ;;
            --no-staticcheck)
                RUN_STATICCHECK=false
                shift
                ;;
            --vulncheck)
                RUN_VULNCHECK=true
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
            *)
                print_error "Unknown option: $1"
                show_help
                exit 1
                ;;
        esac
    done
}

setup() {
    print_header "OTLP Go SDK - Lint Script"
    
    # Check Go installation
    if ! command -v go &> /dev/null; then
        print_error "Go is not installed or not in PATH"
        exit 1
    fi
    
    GO_VERSION=$(go version | awk '{print $3}')
    print_info "Go version: ${GO_VERSION}"
    
    # Create directories
    mkdir -p "${LINT_DIR}"
    
    # Change to project root
    cd "${PROJECT_ROOT}"
    
    # Initialize log file
    echo "Lint run started at $(date)" > "${LINT_LOG}"
}

check_gofmt() {
    if [[ "$RUN_GOFMT" == false ]]; then
        return 0
    fi
    
    print_header "Running gofmt"
    
    local unformatted
    unformatted=$(gofmt -l . 2>&1 || true)
    
    if [[ -z "$unformatted" ]]; then
        print_success "All files are properly formatted"
        return 0
    else
        print_error "The following files need formatting:"
        echo "$unformatted"
        echo "$unformatted" >> "${LINT_LOG}"
        
        if [[ "$FIX_ISSUES" == true ]]; then
            print_info "Auto-formatting files..."
            echo "$unformatted" | xargs gofmt -w
            print_success "Files formatted"
            return 0
        fi
        
        return 1
    fi
}

check_govet() {
    if [[ "$RUN_GOVET" == false ]]; then
        return 0
    fi
    
    print_header "Running go vet"
    
    local failed=0
    local total=0
    
    for module in "${MODULES[@]}"; do
        print_info "Vetting: ${module}"
        
        if go vet "${module}"; then
            print_success "Vet passed: ${module}"
        else
            print_error "Vet failed: ${module}"
            failed=$((failed + 1))
        fi
        total=$((total + 1))
    done
    
    if [[ $failed -eq 0 ]]; then
        print_success "go vet passed for all modules"
        return 0
    else
        print_error "go vet failed for ${failed}/${total} modules"
        return 1
    fi
}

check_golangci_lint() {
    if [[ "$RUN_GOLANGCI_LINT" == false ]]; then
        return 0
    fi
    
    print_header "Running golangci-lint"
    
    # Check if golangci-lint is installed
    if ! command -v golangci-lint &> /dev/null; then
        print_warning "golangci-lint not found. Installing..."
        
        # Try to install
        if command -v brew &> /dev/null; then
            brew install golangci-lint 2>/dev/null || true
        else
            # Install via curl
            curl -sSfL https://raw.githubusercontent.com/golangci/golangci-lint/master/install.sh | sh -s -- -b "$(go env GOPATH)/bin" 2>/dev/null || true
        fi
        
        # Check again
        if ! command -v golangci-lint &> /dev/null; then
            print_warning "Could not install golangci-lint, skipping"
            return 0
        fi
    fi
    
    local golangci_version
    golangci_version=$(golangci-lint --version 2>/dev/null | head -n 1 || echo "unknown")
    print_info "Using: ${golangci_version}"
    
    local lint_args=()
    
    if [[ "$VERBOSE" == true ]]; then
        lint_args+=("-v")
    fi
    
    if [[ "$FIX_ISSUES" == true ]]; then
        lint_args+=("--fix")
    fi
    
    # Create config if not exists
    if [[ ! -f ".golangci.yml" && ! -f ".golangci.yaml" ]]; then
        print_info "Creating default golangci-lint config..."
        cat > "${PROJECT_ROOT}/.golangci.yml" << 'EOF'
run:
  timeout: 5m
  go: '1.26'

linters:
  enable:
    - gofmt
    - govet
    - errcheck
    - staticcheck
    - gosimple
    - ineffassign
    - typecheck
    - unused
    - misspell
    - gosec
    - unconvert
    - gocritic

linters-settings:
  gofmt:
    simplify: true
  govet:
    enable-all: true
  errcheck:
    check-blank: true
  gocritic:
    enabled-tags:
      - performance
      - style
      - experimental

issues:
  exclude-use-default: false
  max-issues-per-linter: 50
  max-same-issues: 10
EOF
    fi
    
    if golangci-lint run "${lint_args[@]}" ./...; then
        print_success "golangci-lint passed"
        return 0
    else
        print_error "golangci-lint found issues"
        return 1
    fi
}

check_staticcheck() {
    if [[ "$RUN_STATICCHECK" == false ]]; then
        return 0
    fi
    
    print_header "Running staticcheck"
    
    # Check if staticcheck is installed
    if ! command -v staticcheck &> /dev/null; then
        print_warning "staticcheck not found. Installing..."
        go install honnef.co/go/tools/cmd/staticcheck@latest 2>/dev/null || true
        
        # Check again
        if ! command -v staticcheck &> /dev/null; then
            print_warning "Could not install staticcheck, skipping"
            return 0
        fi
    fi
    
    local staticcheck_version
    staticcheck_version=$(staticcheck -version 2>/dev/null | head -n 1 || echo "unknown")
    print_info "Using: ${staticcheck_version}"
    
    if staticcheck ./...; then
        print_success "staticcheck passed"
        return 0
    else
        print_error "staticcheck found issues"
        return 1
    fi
}

check_vulncheck() {
    if [[ "$RUN_VULNCHECK" == false ]]; then
        return 0
    fi
    
    print_header "Running govulncheck"
    
    # Check if govulncheck is installed
    if ! command -v govulncheck &> /dev/null; then
        print_warning "govulncheck not found. Installing..."
        go install golang.org/x/vuln/cmd/govulncheck@latest 2>/dev/null || true
        
        # Check again
        if ! command -v govulncheck &> /dev/null; then
            print_warning "Could not install govulncheck, skipping"
            return 0
        fi
    fi
    
    if govulncheck ./...; then
        print_success "govulncheck passed"
        return 0
    else
        print_warning "govulncheck found potential vulnerabilities"
        return 0  # Don't fail on vulncheck, just warn
    fi
}

check_cyclomatic() {
    print_header "Checking cyclomatic complexity"
    
    # Check if gocyclo is installed
    if ! command -v gocyclo &> /dev/null; then
        print_warning "gocyclo not found, installing..."
        go install github.com/fzipp/gocyclo/cmd/gocyclo@latest 2>/dev/null || true
    fi
    
    if command -v gocyclo &> /dev/null; then
        local complex_funcs
        complex_funcs=$(gocyclo -over 15 . 2>/dev/null | grep -v "_test.go" | head -10 || true)
        
        if [[ -n "$complex_funcs" ]]; then
            print_warning "Functions with high cyclomatic complexity (>15):"
            echo "$complex_funcs"
        else
            print_success "No high complexity functions found"
        fi
    else
        print_warning "Skipping cyclomatic complexity check"
    fi
}

print_summary() {
    print_header "Lint Summary"
    
    local log_content
    if [[ -f "${LINT_LOG}" ]]; then
        log_content=$(cat "${LINT_LOG}")
        if [[ -n "$log_content" ]]; then
            print_info "Issues logged to: ${LINT_LOG}"
        fi
    fi
    
    print_success "Linting completed!"
}

main() {
    parse_args "$@"
    setup
    
    local exit_code=0
    
    # Run all checks
    if ! check_gofmt; then
        exit_code=1
    fi
    
    if ! check_govet; then
        exit_code=1
    fi
    
    if ! check_golangci_lint; then
        exit_code=1
    fi
    
    if ! check_staticcheck; then
        exit_code=1
    fi
    
    check_vulncheck || true  # Don't fail on vulncheck
    check_cyclomatic || true  # Don't fail on complexity
    
    print_summary
    
    if [[ $exit_code -ne 0 ]]; then
        print_error "Linting found issues. Please fix them."
        exit 1
    fi
}

# Run main function
trap 'print_error "Linting interrupted"; exit 1' INT TERM
main "$@"
