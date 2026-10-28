module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FixedCoordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.Criteria
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.NormalWeights
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.FiniteBound.SliceCounts

/-!
# Assembling the normal elementary fixed-mask bound

Choose a nonidentity element of a nontrivial normal elementary subgroup B
whose candidate weight is least. All of B lies in its weighted commuting
slice. If the normality certificate bounds the common fixed masks by that
weight and the finite slice certificate bounds the product by 1024, then
`|B| * |FixedMasks B| ≤ 1024`.

The minimum is chosen by the least-number principle, so this abstract
argument does not expand the concrete 1024-element enumeration. Pointwise
permutation commutativity is first proved for abstract permutations to avoid
reducing literal tables while checking the algebraic argument.

Both certificates refer to the actual Sylow subgroup and the exact row action
in `FixedCoordinates`. `NormalWeights` proves the fixed-mask estimates using
checked conjugates and row equations; `SliceCounts` proves the finite bounds
using checked weight-threshold counts. Assembling these certificates gives
the unconditional `normalElementaryFixedBound`.
The literal ATLAS provenance is documented in `QuotientInvolutions.SylowData`
and `Image.StarData`; no ambient classification result is used.
-/

public section
namespace Janko4.LocalStructure.SylowCore
open Simplicity.Max1Fusion.QuotientInvolutions
open FiniteBoundCertificate

private theorem least_weight (B : Subgroup sylowCandidate) (hne : B ≠ ⊥) :
    ∃ i : Index, element i ∈ B ∧ i ≠ identityIndex ∧
      ∀ j, element j ∈ B → weight i ≤ weight j := by
  classical
  have hex : ∃ n : ℕ, ∃ i : Index,
      element i ∈ B ∧ i ≠ identityIndex ∧ weight i = n := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨i, hi⟩ := element_bijective.surjective b.val
    refine ⟨weight i, i, ?_, ?_, rfl⟩
    · rw [hi]
      exact b.property
    · intro hid
      apply hb
      apply Subtype.ext
      rw [← hi, hid, element_identityIndex]
      rfl
  obtain ⟨i, hiB, hi1, hiw⟩ := Nat.find_spec hex
  refine ⟨i, hiB, hi1, ?_⟩
  intro j hj
  by_cases hj1 : j = identityIndex
  · subst j
    exact weight_le_identityIndex i
  · rw [hiw]
    exact Nat.find_min' hex ⟨j, hj, hj1, rfl⟩

private theorem perm_point_commute {X : Type*} (u v : Equiv.Perm X)
    (h : u * v = v * u) (p : X) : u (v p) = v (u p) :=
  congrArg (fun q : Equiv.Perm X => q p) h

private theorem slice_mem (B : Subgroup sylowCandidate) [IsElementaryAbelian 2 B]
    (i : Index) (hiB : element i ∈ B)
    (hle : ∀ j, element j ∈ B → weight i ≤ weight j)
    (j : Index) (hj : element j ∈ B) : sliceTest i j := by
  refine ⟨hle j hj, ?_⟩
  have hcomm := congrArg permHom (setLike_mul_comm hiB hj)
  simp only [map_mul, permHom_element] at hcomm
  intro p
  exact perm_point_commute (perm i) (perm j) hcomm (p.castLE (by decide))

private theorem card_le_slice (B : Subgroup sylowCandidate) (i : Index)
    (h : ∀ j, element j ∈ B → sliceTest i j) : Nat.card B ≤ Nat.card (Slice i) := by
  classical
  let f : B → Slice i := fun b =>
    ⟨enumeration.symm b.val, h _ (by
      rw [element_enumeration_symm]
      exact b.property)⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  apply Subtype.ext
  apply enumeration.symm.injective
  exact congrArg Subtype.val hab

/-- The two independent finite certificates imply the published fixed-mask bound. -/
theorem normalElementaryFixedBound_of_certificates
    (hfixed : NormalFixedCertificate) (hslice : SliceCertificate) :
    NormalElementaryFixedBound := by
  intro B hnormal helem hne
  let : IsElementaryAbelian 2 B := helem
  obtain ⟨i, hiB, hi1, hle⟩ := least_weight B hne
  exact (Nat.mul_le_mul (card_le_slice B i (slice_mem B i hiB hle))
    (hfixed B hnormal helem i hiB)).trans (hslice i hi1)

/-- Every nontrivial normal elementary two-subgroup of the literal Sylow candidate
has order times its number of common fixed row-coordinate masks at most 1024. -/
theorem normalElementaryFixedBound : NormalElementaryFixedBound :=
  normalElementaryFixedBound_of_certificates normalFixedCertificate sliceCertificate

end Janko4.LocalStructure.SylowCore
