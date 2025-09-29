# syntax=docker/dockerfile:1

FROM golang:1.25 as builder
WORKDIR /app
COPY go.mod go.sum ./
RUN go mod download
COPY . .
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build -o /out/app ./src

FROM gcr.io/distroless/base-debian12
WORKDIR /
COPY --from=builder /out/app /app
EXPOSE 8080
ENV OTLP_GRPC_ENDPOINT=collector:4317
USER nonroot:nonroot
ENTRYPOINT ["/app"]

