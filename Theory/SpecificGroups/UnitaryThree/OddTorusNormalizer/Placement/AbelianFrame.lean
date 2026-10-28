module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.Geometry
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.CubicExclusion
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.CanonicalFrame
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The abelian branch of odd unitary frame placement

The normalizing involution excludes an irreducible abelian action on the
natural three-dimensional space, directly in characteristic two. The source
cardinality hypothesis supplies that characteristic; neither odd order nor
no-Borel exclusion is needed for this first reduction.

Spectral descent of the resulting reducible action constructs a common
eigenbasis over the original field. No-Borel exclusion rules out repeated
weights, and orthogonalization identifies all common eigenlines with the
three lines of an orthonormal frame over that field. The subgroup's normalizer
permutes these lines. Thus the subgroup together with its normalizing
involution stabilizes this frame and normalizes its literal special frame
torus. Every spectral and geometric premise is discharged here.

Source: GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open BenderSuzuki.MatrixGroups Representation
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E] [Finite E]

/-- Under the source field-cardinality hypothesis, a normalizing involution
excludes irreducibility of the actual abelian special-unitary action. -/
theorem special_not_irreducible_of_abelian_normalizing_involution
    (J : HermitianForm 3 E) {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) [IsMulCommutative H]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ Subgroup.normalizer H) :
    ¬ IsIrreducible ((AbelianFrame.specialNatural J).comp H.subtype) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  intro hirr
  let : IsIrreducible ((AbelianFrame.specialNatural J).comp H.subtype) := hirr
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ht1 := AbelianFrame.involution_eq_one_of_normalizes_irreducible_abelian
    (AbelianFrame.specialNatural J) (AbelianFrame.specialNatural_injective J)
    (by simp) H t ht2 htH
  simp [ht1] at ht

/-- The abelian branch of GLS4, Chapter 4, Lemma 3.11(a): an odd abelian
special-unitary subgroup, excluded from all isotropic-line stabilizers and
normalized by an involution, preserves an orthonormal frame together with
that involution. The frame is defined over the original matrix field. -/
theorem special_frame_of_abelian
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ Subgroup.normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J, H ⊔ Subgroup.zpowers t ≤ specialFrameStabilizer J P := by
  have hred := special_not_irreducible_of_abelian_normalizing_involution J hcard H t ht htH
  obtain ⟨b, hb⟩ := AbelianFrame.exists_commonEigenbasis_of_reducible
    J hn hcard hfixed H hodd hB hred
  obtain ⟨P, hP⟩ := AbelianFrame.exists_frame_eq_commonEigenlines
    J hn hcard hfixed H hB b hb
  exact ⟨P, AbelianFrame.special_frame_of_commonEigenlines J H t htH P hP⟩

/-- The abelian geometric branch places the actual subgroup and involution
in the normalizer of the torus attached to the constructed orthonormal frame. -/
theorem special_placement_of_abelian
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (t : J.specialSubgroup) (ht : orderOf t = 2)
    (htH : t ∈ Subgroup.normalizer H) (hB : SpecialNoBorel J H) :
    ∃ P : OrthogonalFrame J,
      H ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (specialFrameTorus J P) := by
  obtain ⟨P, hP⟩ := special_frame_of_abelian J hn hcard hfixed H hodd t ht htH hB
  exact ⟨P, hP.trans (specialFrameStabilizer_le_normalizer J P)⟩

end UnitaryThree.OddTorusNormalizer
