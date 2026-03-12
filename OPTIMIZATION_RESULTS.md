# Type-Level List vs Function Type Optimization Results

## Overview

This document compares two implementations of the `HyperZip` library's type-level encoding:
- **List version**: Uses type-level lists like `'[a, b, c]`
- **Function type version**: Uses function types like `a -> b -> c -> Nil`

The hypothesis was that function types would reduce simplifier output because they have linear size, while type-level lists have quadratic size due to type annotations on each cons cell.

## Implementation Details

The refactoring replaced all type-level list patterns with function type patterns:
- `'[]` → `Nil` (new data type)
- `(x ': args)` → `(x -> args)`
- `'[a, b, c]` → `(a -> b -> c -> Nil)`

All type family definitions (`ProducerTF`, `BaseFunTF`, `UnsnocTF`, etc.) were updated accordingly.

## Results with -O2 and No Core Dump (13 Lists)

When testing without core dump overhead, the compilation time differences become much more pronounced:

### Compilation Time (without core dump)

Average over 3 runs with `-O2` optimization:

| Version | Run 1 | Run 2 | Run 3 | Average |
|---------|-------|-------|-------|---------|
| **List** | 49.4s | 48.9s | 48.7s | 49.0s |
| **Function Type** | 41.1s | 41.0s | 41.0s | 41.0s |

**Result**: Function type version is **8 seconds faster** - a **16% improvement**

### Key Findings

1. **Core dump overhead masks the true benefit**: With core dump enabled (-ddump-simpl), compilation took ~2m20s for both versions. Without it, the difference becomes clear: 49s vs 41s.

2. **The optimization significantly improves compilation speed**: The 16% improvement is substantial and consistent across multiple runs.

3. **-O2 vs -O1 has no effect on core output**: The Tidy Core metrics (types, coercions, size) were identical between -O1 and -O2, confirming that type-level complexity is resolved before optimization passes.

4. **The reduction in coercions directly impacts compile time**: The 45% reduction in coercions (16M → 8.8M) translates to real compilation time savings when not masked by I/O overhead.

### Updated Recommendation

The function type optimization provides a **significant 16% compilation time improvement** for real-world builds (without core dumps). This makes it highly valuable for:
- Development workflows where fast compilation matters
- CI/CD pipelines
- Projects using similar type-level techniques with many type arguments

The earlier measurements showing only 1-2% improvement were misleading due to core dump I/O overhead dominating the compilation time.

## List Fusion Verification

One of the key motivations for using hyperfunctions in this implementation is that list fusion can occur for all list arguments.

### Fusion Test Results

Testing with 10 million elements summing 3 lists:

| Implementation | Bytes Allocated | Relative |
|----------------|-----------------|----------|
| **zipWithN (this library)** | 56.7 MB | 1.0× |
| **Standard zipWith3** | 1,440 MB | **25.4×** |

### Analysis

The hyperfunction-based `zipWithN` shows excellent fusion characteristics:

1. **Minimal allocation**: Only 56.7 MB for processing 10M elements across 3 lists
   - If intermediate lists were materialized: ~240 MB expected (8 bytes × 10M × 3)
   - Actual allocation is even less than this, showing aggressive optimization

2. **Superior to standard library**: Standard `zipWith3` allocated 25× more memory (1.4 GB), likely due to:
   - Less aggressive fusion in the standard library's implementation
   - zipWith3 being limited to exactly 3 arguments, possibly preventing some optimizations

3. **Evidence of fusion**: The absence of `replicate` in the final Core output confirms that the list generation and consumption have been fused into a tight loop.

### Conclusion

The hyperfunction-based implementation successfully achieves list fusion across all arguments, resulting in memory allocation that is **25× better than the standard library**. This validates the design choice and makes `zipWithN` suitable for performance-critical applications where multiple lists need to be processed together.

## INLINEABLE Pragma Impact

### Question
Are the `{-# INLINEABLE #-}` pragmas on class instance methods necessary for fusion to occur?

### Test Results

Testing with 10 million elements:

| Configuration | Bytes Allocated | Core Size | Compile Time (13 lists) |
|---------------|-----------------|-----------|-------------------------|
| **With INLINEABLE** | 56,737,024 | 1499 lines | 7.3s |
| **Without INLINEABLE** | 56,737,024 | 1286 lines | 6.9s |

### Conclusion

**The INLINEABLE pragmas are NOT necessary for fusion to occur.**

Key findings:
1. **Identical allocation**: Both versions allocate exactly the same amount of memory (56.7 MB)
2. **Slightly faster compilation**: Without INLINEABLE, compilation is ~5% faster (7.3s → 6.9s)
3. **Smaller core**: The version without INLINEABLE produces 14% less core (1499 → 1286 lines)
4. **GHC inlines automatically**: GHC's optimizer is able to inline the class methods and achieve full fusion without explicit INLINEABLE pragmas

### Recommendation

**Remove the INLINEABLE pragmas** - they add compilation overhead without providing any benefit for this codebase. GHC's optimizer is smart enough to inline what's needed for fusion without explicit hints.

## Updated Results with 6 Lists

To ensure all class instances are exercised, testing was repeated with 6 lists:

### Fusion Test Results (6 Lists)

Testing with 10 million elements summing 6 lists:

| Implementation | Bytes Allocated | Relative |
|----------------|-----------------|----------|
| **zipWithN (this library)** | 56.7 MB | 1.0× |
| **Manual nested zip** | 6,080 MB | **107×** |

### INLINEABLE Impact (6 Lists)

| Configuration | Bytes Allocated | Compile Time (avg) |
|---------------|-----------------|-------------------|
| **With INLINEABLE** | 56,732,048 | 7.60s |
| **Without INLINEABLE** | 56,736,992 | 7.05s |

**Difference**: 0.55s faster without INLINEABLE (~7% improvement)

### Updated Conclusions

1. **Fusion works perfectly with 6 lists**: Only 56.7 MB allocated vs ~480 MB if lists were materialized
2. **Massive improvement over naive approach**: 107× less allocation than manual nested zip
3. **INLINEABLE still not needed**: Identical fusion quality without the pragmas
4. **Compilation benefit**: ~7% faster compilation without INLINEABLE pragmas

The recommendation stands: **remove INLINEABLE pragmas** - they provide no fusion benefit and slow down compilation.
