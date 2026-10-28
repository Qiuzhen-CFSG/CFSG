module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Unipotent
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.Inputs
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.HighestWeight
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FixedLine

/-!
# Finite highest-vector reductions for D4

The positive finite unipotent subgroup is proved to be a two-group in
`Unipotent`. The fixed-line criterion therefore reduces finite irreducibility
to highest-line detection and spanning by the elementary orbit. Independently,
a finite intertwiner carries a highest vector to the highest line once that
line is detected. Rescaling preserves its actual algebraic highest weight;
root-action recovery on these vectors then gives weight separation.

The finite highest-line, orbit-span, and root-action recovery statements remain
explicit inputs from `Inputs`. These conditional theorems do not assert GLS3
Theorem 2.8.2 before those inputs have been proved. Every assertion uses the
literal elementary subgroup, including when the exponent is one.

Sources: GLS3, Theorem 2.8.2; Steinberg, `Chapter2St2.tex`, Theorem 13.3(a).
-/

@[expose] public noncomputable section

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Every nonzero vector on an actual highest line has that highest weight. -/
theorem hasHighWeight_of_mem_highestLine (S : Geometry K) (A : RationalFactor K)
    {a : Weight} {v w : A.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (hw0 : w ≠ 0) (hw : w ∈ Submodule.span k ({v} : Set A.Space)) :
    HasHighWeight A.action S.bigCell.data.B S.torus w (S.coordinateEmbedding a) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  refine ⟨⟨hw0, ?_⟩, hw0, ?_⟩
  · intro g hg
    obtain ⟨d, hd⟩ := hv.1.2 g hg
    refine ⟨d, ?_⟩
    rw [← hc, map_smul, hd, smul_comm]
  · intro t
    rw [← hc, map_smul, hv.2.2 t, smul_comm]

/-- Finite intertwining carries a rational highest vector into the target
highest line when finite positive-unipotent invariants detect that line. -/
theorem intertwiner_highestVector_mem_highestLine (S : Geometry K) (n : ℕ)
    (hline : FiniteHighestLine S n) (A C : RationalFactor K)
    {a b : Weight} (hbr : InRestrictedRange n b) {v : A.Space} {w : C.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (hw : HasHighWeight C.action S.bigCell.data.B S.torus w (S.coordinateEmbedding b))
    (e : Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) :
    e v ∈ Submodule.span k ({w} : Set C.Space) := by
  apply hline C b hbr w hw (e v)
  intro g
  calc
    (C.restrict (S.inclusion n)).ρ g.val (e v) =
        e ((A.restrict (S.inclusion n)).ρ g.val v) :=
      (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g.val v).symm
    _ = e v := congrArg e (highestVector_fixed_positiveUnipotent S A hv n g)

/-- The transported highest vector has the target algebraic highest weight.
This uses line detection, not any extension of the finite intertwiner. -/
theorem intertwiner_hasHighWeight (S : Geometry K) (n : ℕ)
    (hline : FiniteHighestLine S n) (A C : RationalFactor K)
    {a b : Weight} (hbr : InRestrictedRange n b) {v : A.Space} {w : C.Space}
    (hv : HasHighWeight A.action S.bigCell.data.B S.torus v (S.coordinateEmbedding a))
    (hw : HasHighWeight C.action S.bigCell.data.B S.torus w (S.coordinateEmbedding b))
    (e : Representation.Equiv (A.restrict (S.inclusion n)).ρ
      (C.restrict (S.inclusion n)).ρ) :
    HasHighWeight C.action S.bigCell.data.B S.torus (e v) (S.coordinateEmbedding b) := by
  apply hasHighWeight_of_mem_highestLine S C hw
  · exact fun h => hv.1.1 (e.toLinearEquiv.map_eq_zero_iff.mp h)
  · exact intertwiner_highestVector_mem_highestLine S n hline A C hbr hv hw e

/-- Highest-line detection and finite cyclicity imply the exact restricted
irreducibility contract. The two-group premise is discharged geometrically. -/
theorem restrictedIrreducibility_of_finiteHighestLine_of_orbitSpan
    (S : Geometry K) (n : ℕ) (hn : 0 < n)
    (hline : FiniteHighestLine S n) (hspan : FiniteHighestOrbitSpan S n) :
    RestrictedIrreducibility S n := by
  intro A a har ha
  obtain ⟨v, hv⟩ := ha
  let := S.elementary_finite n hn
  let : Nontrivial (A.restrict (S.inclusion n)) := inferInstanceAs (Nontrivial A.Space)
  exact irreducible_of_fixedLine_of_orbitSpan
    (A.restrict (S.inclusion n)).ρ (positiveUnipotent S n)
    (positiveUnipotent_isPGroup S n) v (hline A a har v hv) (hspan A a har v hv)

/-- Once finite invariants detect the highest line, root-action recovery
for highest vectors proves the exact separation contract. No exhaustivity or
finite irreducibility result is used. -/
theorem restrictedSeparation_of_finiteHighestLine_of_weightRecovery
    (S : Geometry K) (n : ℕ)
    (hline : FiniteHighestLine S n) (hweight : HighestVectorWeightRecovery S n) :
    RestrictedSeparation S n := by
  intro A C a b har hbr ha hb he
  obtain ⟨v, hv⟩ := ha
  obtain ⟨w, hw⟩ := hb
  obtain ⟨e⟩ := he
  exact hweight A C a b har hbr v (e v) hv
    (intertwiner_hasHighWeight S n hline A C hbr hv hw e) e rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
