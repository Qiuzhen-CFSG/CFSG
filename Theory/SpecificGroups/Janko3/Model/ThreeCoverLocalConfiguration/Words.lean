module

public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Generators
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Marked words for the J₃ affine three-cover configuration

The scalar `x`, the two generators of `rightSupport`, and `y` are short
words in the seven affine generators. The left support is the image of the
fixed involution-centralizer candidate under conjugation by a model word.
These definitions assert no perfectness, order, or normalization properties.
The proofs of those properties are separate finite permutation certificates.

Source: GLS, Number 3, Table 5.3h, printed p.269; Aschbacher--Smith,
A.2.19, printed p.41, and I.2.1, printed p.409. The untrusted discovery data
from the parent construction are preserved verbatim under `source/`.
GAP maps are retained as inverse maps, so multiplication of the Lean words
has the same order as the GAP words; GAP conjugation by g corresponds to
Lean conjugation by g⁻¹.
-/

namespace Sporadic.Janko3.ThreeCoverConfig
open TwoLocal

@[expose] public def x : Model := affineGenerator 5 ^ 2

@[expose] public def d0 : Model :=
  (affineGenerator 6)⁻¹ * (affineGenerator 2)⁻¹ *
    (affineGenerator 4)⁻¹ ^ 2 * (affineGenerator 5)⁻¹

@[expose] public def d1 : Model :=
  affineGenerator 2 * (affineGenerator 5)⁻¹ *
    (affineGenerator 6)⁻¹ * affineGenerator 4

@[expose] public def y : Model :=
  affineGenerator 0 * (affineGenerator 6)⁻¹ * (affineGenerator 5)⁻¹ ^ 3

@[expose] public def conjugator : Model :=
  chainElement [0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0] [1, 0, 1, 2, 1, 0, 0, 1, 2, 1, 0, 1, 0, 0, 1] [2, 0, 0]

/-- The marked translation subgroup in the affine candidate. -/
@[expose] public def twoSubgroup : Subgroup Model := elementaryCandidate

/-- The image of the fixed involution-centralizer candidate under conjugation. -/
@[expose] public def leftSupport : Subgroup Model :=
  centralizerCandidate.map (MulAut.conj conjugator).toMonoidHom

/-- The marked two-generator complement subgroup. -/
@[expose] public def rightSupport : Subgroup Model :=
  Subgroup.closure ({d0, d1} : Set Model)

public theorem d0_mem : d0 ∈ rightSupport := Subgroup.subset_closure (by simp)
public theorem d1_mem : d1 ∈ rightSupport := Subgroup.subset_closure (by simp)

end Sporadic.Janko3.ThreeCoverConfig
