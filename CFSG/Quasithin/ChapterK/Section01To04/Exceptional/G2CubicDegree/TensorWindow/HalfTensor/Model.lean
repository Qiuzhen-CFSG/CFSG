module

public import Theory.Representation.G2.TensorClassification.Construction

/-!
# The concrete pair of natural G₂ factors

Both factors are scalar extensions of the trace-zero octonion quotient. Their
actual group actions are precomposed with Frobenius at positions `i` and `i+s`.
For a defining field of degree `2*s`, these are the two conjugate factors in
the half-field tensor case. The carrier and action are specified independently
of the still-needed recognition and normalizer calculations.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
variable (F K : Type*) [Field F] [Finite F] [CharP F 2]
  [Field K] [Algebra F K]

abbrev NaturalScalarSpace := K ⊗[F] Atlas.G2.Natural.Space F
abbrev PairSpace := NaturalScalarSpace F K ⊗[K] NaturalScalarSpace F K

@[expose] def naturalTwist (i : ℕ) :
    Representation K (Atlas.G2.Model F) (NaturalScalarSpace F K) :=
  (Representation.extendScalars K (Atlas.G2.Natural.action F)).comp
    (Atlas.G2.Restricted.frobeniusAutomorphism F i).toMonoidHom

@[expose] def pairRep (i s : ℕ) :
    Representation K (Atlas.G2.Model F) (PairSpace F K) :=
  (naturalTwist F K i).tprod (naturalTwist F K (i + s))

omit [Finite F] in
@[simp] theorem finrank_pairSpace : Module.finrank K (PairSpace F K) = 36 := by
  rw [Module.finrank_tensorProduct, Module.finrank_baseChange,
    Atlas.G2.Natural.finrank_space]

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
