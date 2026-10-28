module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.ReflectionGeneration.NormalizedComplement
public import Mathlib.Algebra.Field.ZMod

/-!
# Binary D4 point-fixers in literal D3 coordinates

The normalized hyperbolic complement of `formD 4 (ZMod 2)` is `formD 3
(ZMod 2)`. Its extension fixes the marked pair and acts on the remaining six
coordinates by the original D3 linear map. The explicit point-root factor then
gives the full orthogonal factorization.

The elementary factorization and its arbitrary-singular-vector specialization
are conditional on the standard complement extension reflecting elementary
membership. They isolate this single missing subgroup-theoretic input without
assuming a point-stabilizer factorization or a model recognition statement.

Source: the hyperbolic-pair parabolic reduction, as used in Aschbacher, Sporadic
Groups (1994), 25.1(4), 25.2 and 25.5(7), pp.132--134. The literal Siegel and
complement maps are the licensed ATLAS adaptations imported below.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic ClassicalOrthogonal.ReflectionGeneration
namespace ClassicalOrthogonal.BinaryD4Parabolic
abbrev Space := VectorD 4 (ZMod 2)
abbrev Form := formD 4 (ZMod 2)
abbrev TailForm := formD 3 (ZMod 2)
abbrev Orthogonal := quadraticIsometrySubgroup Form
abbrev TailOrthogonal := quadraticIsometrySubgroup TailForm
abbrev StandardComplement := complementForm Form (e 0) (f 0)
abbrev standardLift := complementLift Form (e 0) (f 0) (formD_e 0) (formD_f 0) (polarD_ef 0)

variable (e f : Space) (he : Form e = 0) (hf : Form f = 0) (hef : Form.polarBilin e f = 1)
variable (i : Form.IsometryEquiv Form)
variable (hie : i e = ClassicalOrthogonal.e 0) (hif : i f = ClassicalOrthogonal.f 0)

/-- Extend a literal D3 actor in normalized coordinates. -/
def tailLift (k : TailOrthogonal) : Orthogonal :=
  complementLift Form e f he hf hef
    (isometryGroupTransport (normalizedComplementD e f i hie hif).symm k)

theorem tailLift_fix_e (k : TailOrthogonal) : (tailLift e f he hf hef i hie hif k).val e = e :=
  complementLift_fix_e _ _ _ _ _ _ _

theorem tailLift_fix_f (k : TailOrthogonal) : (tailLift e f he hf hef i hie hif k).val f = f :=
  complementLift_fix_f _ _ _ _ _ _ _

/-- The extension acts by the prescribed D3 map on the six actual tail coordinates. -/
theorem tailLift_apply (k : TailOrthogonal) (x : VectorD 3 (ZMod 2)) :
    (tailLift e f he hf hef i hie hif k).val (i.symm (insertD x)) =
      i.symm (insertD (k.val x)) := by
  let j := normalizedComplementD e f i hie hif
  change (complementLift Form e f he hf hef (isometryGroupTransport j.symm k)).val
    (j.symm x).val = (j.symm (k.val x)).val
  rw [complementLift_apply]
  change (j.symm (k.val (j (j.symm x)))).val = _
  rw [j.apply_symm_apply]

theorem tailLift_mem_elementary (k : TailOrthogonal) (hk : k ∈ elementarySubgroup TailForm) :
    tailLift e f he hf hef i hie hif k ∈ elementarySubgroup Form :=
  complementLift_mem_elementary _ _ _ _ _ _ _
    (isometryTransport_mem_elementary _ _ hk)

/-- The full orthogonal factorization already uses actual D3 coordinates.
The asserted elementary membership here is only for the ambient lift. -/
theorem full_factorization (g : Orthogonal) (hg : g ∈ elementarySubgroup Form)
    (hge : g.val e = e) :
    ∃ k : TailOrthogonal,
      tailLift e f he hf hef i hie hif k ∈ elementarySubgroup Form ∧
      g = pointRootFactor Form e f he hf hef g * tailLift e f he hf hef i hie hif k := by
  let c := pointComplementFactor Form e f he hf hef g hge
  let j := normalizedComplementD e f i hie hif
  let k := isometryGroupTransport j c
  have hback : isometryGroupTransport j.symm k = c :=
    (isometryGroupTransport j).symm_apply_apply c
  have hlift : tailLift e f he hf hef i hie hif k = complementLift Form e f he hf hef c := by
    change complementLift Form e f he hf hef (isometryGroupTransport j.symm k) = _
    rw [hback]
  refine ⟨k, ?_, ?_⟩
  · rw [hlift]
    exact pointComplementFactor_lift_mem Form e f he hf hef g hg hge
  · rw [hlift]
    exact point_factorization Form e f he hf hef g hge

/-- Conditional assembly: standard-pair restriction is the sole remaining input.
This is not an unconditional identification of the elementary point stabilizer. -/
theorem factorization_of_standard_restriction
    (hstandard : ∀ k : quadraticIsometrySubgroup StandardComplement,
      standardLift k ∈ elementarySubgroup Form → k ∈ elementarySubgroup StandardComplement)
    (g : Orthogonal) (hg : g ∈ elementarySubgroup Form) (hge : g.val e = e) :
    ∃ k : TailOrthogonal, k ∈ elementarySubgroup TailForm ∧
      g = pointRootFactor Form e f he hf hef g * tailLift e f he hf hef i hie hif k := by
  let c := pointComplementFactor Form e f he hf hef g hge
  have hc : c ∈ elementarySubgroup (complementForm Form e f) :=
    (complementLift_mem_elementary_iff_of_standard hstandard e f he hf hef c).mp
      (pointComplementFactor_lift_mem Form e f he hf hef g hg hge)
  let j := normalizedComplementD e f i hie hif
  refine ⟨isometryGroupTransport j c, isometryTransport_mem_elementary j c hc, ?_⟩
  have hback : isometryGroupTransport j.symm (isometryGroupTransport j c) = c :=
    (isometryGroupTransport j).symm_apply_apply c
  change g = pointRootFactor Form e f he hf hef g *
    complementLift Form e f he hf hef (isometryGroupTransport j.symm (isometryGroupTransport j c))
  rw [hback]
  exact point_factorization Form e f he hf hef g hge

/-- The normalized pair and D3 model are supplied for every nonzero singular vector. -/
theorem singular_factorization_of_standard_restriction
    (hstandard : ∀ k : quadraticIsometrySubgroup StandardComplement,
      standardLift k ∈ elementarySubgroup Form → k ∈ elementarySubgroup StandardComplement)
    (e : Space) (he : e ≠ 0) (hqe : Form e = 0)
    (g : Orthogonal) (hg : g ∈ elementarySubgroup Form) (hge : g.val e = e) :
    ∃ (f : Space) (hf : Form f = 0) (hef : Form.polarBilin e f = 1)
      (i : Form.IsometryEquiv Form) (hie : i e = ClassicalOrthogonal.e 0)
      (hif : i f = ClassicalOrthogonal.f 0) (k : TailOrthogonal),
      k ∈ elementarySubgroup TailForm ∧
      g = pointRootFactor Form e f hqe hf hef g * tailLift e f hqe hf hef i hie hif k := by
  obtain ⟨f, hf, hef⟩ := exists_singular_partnerD e he hqe
  obtain ⟨i, hie, hif⟩ := exists_pair_normalizationD e f hqe hf hef
  obtain ⟨k, hk, hfactor⟩ := factorization_of_standard_restriction e f hqe hf hef i hie hif
    hstandard g hg hge
  exact ⟨f, hf, hef, i, hie, hif, k, hk, hfactor⟩
end ClassicalOrthogonal.BinaryD4Parabolic

