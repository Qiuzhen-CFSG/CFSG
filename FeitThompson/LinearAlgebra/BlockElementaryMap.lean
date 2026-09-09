module

public import Theory.LinearAlgebra.BlockDecomposition

/-! Compatibility shim: the block-elementary-map API lives in
`Theory.LinearAlgebra.BlockDecomposition`. This module is kept so existing
consumers that `import FeitThompson.LinearAlgebra.BlockElementaryMap`
continue to receive the declarations under their old module path. -/
