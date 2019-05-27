# Weaver

## Build

```
git clone https://github.com/weaver-verifier/weaver
cd weaver
cabal new-build weaver
```

## Example

```
cabal new-run weaver -- examples/parallel-sum-1.wvr -m partition-progress -b rr
```
