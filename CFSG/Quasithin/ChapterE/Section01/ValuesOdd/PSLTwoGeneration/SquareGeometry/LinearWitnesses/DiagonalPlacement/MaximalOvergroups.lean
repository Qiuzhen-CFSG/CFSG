module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.Structure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OvergroupModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.SubfieldReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.SymmetricExclusion
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups.PrimeSubfieldNormalizer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups.TorusExtensions
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.OuterPlacement

/-!
# Assembly of the prime-square PGL₂ maximal-overgroup calculation

Dickson's classification of the literal canonical PSL₂ intersection leaves
split dihedral, S₄, and marked prime-subfield PGL₂ intersections. The
normal-four-group argument excludes S₄. The actual subfield normalizer lies
in PSL₂, excluding the marked subfield intersection. Finally, the dihedral
extension theorem identifies the whole maximal overgroup with the full
centralizer of an inner involution, with rotation order q-1 or q+1.

`sylowOvergroupModel_of_square_card` discharges both premises of the retained
conditional assembly, including for p = 3 and p = 5. Its conclusion supplies
exactly `hover` in `concreteGeometryAt_of_overgroups_and_inner_symmetric`.
`outer_escape_of_square_card` applies it to the existing outer four-group
escape theorem with the literal Sylow intersection and inner image. The
parent placement module retains the independent inner S₄ construction.

Source: Aschbacher--Smith A.2.3(2), E.1.2 and E.1.14(6), printed
pp.33, 209--210 and 214, citing Aschbacher (1982), Lemma 4.10.
-/

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups

open Subgroup GorensteinWalter
open PrimeGeometry.Diagonal.MaximalOvergroups

variable {F : Type*} [Field F] [Finite F]

local instance finitePGL : Finite (PGL2 F) := Finite.of_surjective
  Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- Assemble the square-field Dickson exhaustion with the remaining
whole-overgroup extension and prime-subfield normalizer calculations. -/
public theorem sylowOvergroupModel_of_inner_extension_cases
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M)
    (hdihedral : ∀ z : ℕ, 4 ∣ z → z ∣ (Nat.card F - 1) / 2 →
      Nat.card (inner M) = 2 * z → Nonempty (inner M ≃* DihedralGroup z) →
      ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
        Nonempty (M ≃* DihedralGroup n))
    (hnormalizer : ∀ K : Subfield F, Nat.card K = p →
      normalizer ((Glauberman.Dickson.h826_pglMap K.subtype).range : Set (PGL2 F)) ≤
        innerRange F) :
    PrimeGeometry.Diagonal.SylowOvergroupModel F M := by
  rcases inner_square_dickson_cases hpodd hFcard T M hTM hM.ne_top with
    hdihedralCase | hsymmetricCase | hsubfieldCase
  · obtain ⟨z, h4z, hz, hc, he⟩ := hdihedralCase
    exact Or.inr (hdihedral z h4z hz hc he)
  · exact (inner_not_symmetric_four hpodd hFcard T M hTM hsymmetricCase).elim
  · obtain ⟨⟨e⟩, ⟨w⟩⟩ := hsubfieldCase
    exact (no_subfield_case_of_normalizer_le_inner hpodd hFcard T M hTM
      hnormalizer e w).elim

/-- Apply the conditional maximal-overgroup result to the existing outer
four-group escape theorem, preserving the original Sylow and inner image. -/
public theorem outer_escape_of_inner_extension_cases
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlarge : 5 < p ^ 2)
    (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (A M : Subgroup (PGL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup _))
    (hAJ : ¬ A ≤ innerRange F) (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M)
    (hdihedral : ∀ z : ℕ, 4 ∣ z → z ∣ (Nat.card F - 1) / 2 →
      Nat.card (inner M) = 2 * z → Nonempty (inner M ≃* DihedralGroup z) →
      ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
        Nonempty (M ≃* DihedralGroup n))
    (hnormalizer : ∀ K : Subfield F, Nat.card K = p →
      normalizer ((Glauberman.Dickson.h826_pglMap K.subtype).range : Set (PGL2 F)) ≤
        innerRange F) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  have hF := oddPrimePower_of_square_card hpodd hFcard
  have hcard : 3 < Nat.card F := by omega
  apply PrimeGeometry.Diagonal.outer_kleinFour_escape_of_overgroup_model
    F hF hcard T A M hA hAT ?_ hTM
      (sylowOvergroupModel_of_inner_extension_cases hpodd hFcard T M hM hTM
        hdihedral hnormalizer)
  rwa [pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hcard]

/-- Every maximal subgroup of odd prime-square PGL₂ containing an ambient
Sylow two-subgroup has an actual full torus-normalizer model. In particular,
this supplies `hover` in `concreteGeometryAt_of_overgroups_and_inner_symmetric`
without a subgroup-classification or normalizer premise. -/
public theorem sylowOvergroupModel_of_square_card
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlarge : 5 < p ^ 2)
    (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (M : Subgroup (PGL2 F))
    (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) :
    PrimeGeometry.Diagonal.SylowOvergroupModel F M := by
  have hF := oddPrimePower_of_square_card hpodd hFcard
  have hcard : 3 < Nat.card F := by omega
  apply sylowOvergroupModel_of_inner_extension_cases hpodd hFcard T M hM hTM
  · intro z _h4z _hz hc he
    exact torusModel_of_inner_dihedral hF hcard T M hM hTM hc he
  · intro K hKcard
    exact prime_subfield_normalizer_le_inner hpodd hFcard K hKcard

/-- An outer four-group in an ambient Sylow two-subgroup has a local model
escaping every maximal overgroup of that Sylow in odd prime-square PGL₂.
The model classification and subfield normalizer bound are fully discharged. -/
public theorem outer_escape_of_square_card
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlarge : 5 < p ^ 2)
    (hFcard : Nat.card F = p ^ 2)
    (T : Sylow 2 (PGL2 F)) (A M : Subgroup (PGL2 F))
    (hA : IsKleinFour A) (hAT : A ≤ (T : Subgroup _))
    (hAJ : ¬ A ≤ innerRange F) (hM : IsCoatom M) (hTM : (T : Subgroup _) ≤ M) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      PrimeGeometry.LocalModel A H ∧ ¬ H ≤ M := by
  have hF := oddPrimePower_of_square_card hpodd hFcard
  have hcard : 3 < Nat.card F := by omega
  apply PrimeGeometry.Diagonal.outer_kleinFour_escape_of_overgroup_model
    F hF hcard T A M hA hAT ?_ hTM
      (sylowOvergroupModel_of_square_card hpodd hlarge hFcard T M hM hTM)
  rwa [pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hcard]


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses.DiagonalPlacement.MaximalOvergroups
