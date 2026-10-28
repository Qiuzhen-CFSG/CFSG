module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import Theory.SpecificGroups.SU3.OddRootFixers

/-!
# Marked odd root fixers in actual unitary covers

Actual group equivalences transport the automorphism, its order, the Sylow
subgroup and the full embedded center. The fixed PSL₂ subgroup is pulled
back through the same equivalence. The two branches retain SU₃ itself and
its projective image separately, with both field orders.

The `of_diagonal_forms` export is conditional on the two intrinsic matrix
normal forms. The `unitary_cover_odd_root_fixed_linear` export below supplies
those forms from odd order and pointwise fixation through the intrinsic
theorems, and is the unconditional model input required by
`CosetLinearWitness`.

Source: GLS4, Chapter 2, proof of Lemma 13.2, using Chapter 4, Lemma 3.6(c,d).
-/

public section
namespace BenderSuzuki.ZD.UnitaryExclusion.CosetLinearWitness
open Subgroup _root_.BenderSuzuki.MatrixGroups
open HermitianForm.OddRootFixers

/-- Transport the intrinsic marked block construction to either actual cover.
The explicit normal-form premises remain obligations of the intrinsic theorem. -/
theorem unitary_cover_odd_root_fixed_linear_of_diagonal_forms {n : ℕ} (hn : 2 ≤ n)
    (hspecial : ∀ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E)
      (hJ : J.form = !![0,0,1;0,1,0;1,0,0]),
      Nat.card E = (2 ^ n) ^ 2 → Nat.card {x : E // J.conj x = x} = 2 ^ n →
      ∀ (P : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup),
      Odd (orderOf a) →
      (∀ x ∈ (center P).map (P : Subgroup J.specialSubgroup).subtype, a x = x) →
      HasSpecialRootForm J hJ (IsRootDiagonal J) P a)
    (hprojective : ∀ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E)
      (hJ : J.form = !![0,0,1;0,1,0;1,0,0]),
      Nat.card E = (2 ^ n) ^ 2 → Nat.card {x : E // J.conj x = x} = 2 ^ n →
      ∀ (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
        (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)),
      Odd (orderOf a) →
      (∀ x ∈ (center P).map
        (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype, a x = x) →
      HasProjectiveRootForm J hJ (IsRootDiagonal J) P a)
    {H : Type*} [Group H] [Finite H] (hcover : IsUnitaryCentralizerCoverAt n H)
    (P : Sylow 2 H) (a : MulAut H) (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map (P : Subgroup H).subtype, a x = x) :
    ∃ I : Subgroup H, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup H).subtype ≤ I ∧ ∀ x ∈ I, a x = x := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hp | hs⟩ := hcover
  · obtain ⟨e⟩ := hp
    apply sylow_fixed_subgroup_of_equiv e P a
    apply projective_fixed_linear_of_diagonal_form J hJ hn hcard hfixed
    apply hprojective E inferInstance inferInstance J hJ hcard hfixed
    · simpa only [MulEquiv.orderOf_eq] using ha
    · exact fixes_sylow_center_congr e P a hfix
  · obtain ⟨e⟩ := hs
    apply sylow_fixed_subgroup_of_equiv e P a
    apply special_fixed_linear_of_diagonal_form J hJ hn hcard hfixed
    apply hspecial E inferInstance inferInstance J hJ hcard hfixed
    · simpa only [MulEquiv.orderOf_eq] using ha
    · exact fixes_sylow_center_congr e P a hfix

/-- The intrinsic odd-order root-fixer theorem transported to either actual cover.

The cover is the source of the field and Hermitian cardinality hypotheses; the
marked Sylow center is transported through the supplied actual equivalence.
-/
theorem unitary_cover_odd_root_fixed_linear {n : ℕ} (hn : 2 ≤ n)
    {H : Type*} [Group H] [Finite H] (hcover : IsUnitaryCentralizerCoverAt n H)
    (P : Sylow 2 H) (a : MulAut H) (ha : Odd (orderOf a))
    (hfix : ∀ x ∈ (center P).map (P : Subgroup H).subtype, a x = x) :
    ∃ I : Subgroup H, Nonempty (I ≃* PSL2BinaryMatrixGroup n) ∧
      (center P).map (P : Subgroup H).subtype ≤ I ∧ ∀ x ∈ I, a x = x := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, hp | hs⟩ := hcover
  · obtain ⟨e⟩ := hp
    apply sylow_fixed_subgroup_of_equiv e P a
    apply projective_fixed_linear_of_odd_root J hJ hn hcard hfixed
    · simpa only [MulEquiv.orderOf_eq] using ha
    · exact fixes_sylow_center_congr e P a hfix
  · obtain ⟨e⟩ := hs
    apply sylow_fixed_subgroup_of_equiv e P a
    apply special_fixed_linear_of_odd_root J hJ hn hcard hfixed
    · simpa only [MulEquiv.orderOf_eq] using ha
    · exact fixes_sylow_center_congr e P a hfix

end BenderSuzuki.ZD.UnitaryExclusion.CosetLinearWitness
