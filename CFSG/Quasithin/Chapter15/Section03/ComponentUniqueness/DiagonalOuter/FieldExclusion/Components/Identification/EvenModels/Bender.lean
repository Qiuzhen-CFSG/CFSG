module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.SU3.SixSubgroupExclusion
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder

/-!
# Excluding the entire Bender catalogue

The marked PSL₃(2) component has a dihedral Sylow two-subgroup. In binary
PSL₂ every Sylow two-subgroup is abelian; in binary PSU₃ every pair of
involutions in a root Sylow subgroup commutes. Neither can contain that
component. Suzuki groups have order prime to three.

This proves the rank-one characteristic-two case without classifying
automorphisms. The unitary parameter is the fixed-field order, so the
coefficient field has order `(2^f)^2`; standard-form transport preserves
the stored involution. Source: Aschbacher--Smith, 15.3.38, printed p.1137,
Theorem C and Remark A.2.4, printed p.33; Huppert II.8.2 and II.10.4--12.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- No binary PSL₂ contains the specified PSL₃(2) component. -/
theorem SimpleInput.not_even_linear_two {n : ℕ} :
    ¬ ClassicalGroup.IsPSL S 2 (2 ^ n) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let P : Sylow 2 PSL(2,F) := default
  obtain ⟨d⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  apply Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => ?_) (e.toMonoidHom.comp (EvenModels.componentEmbedding s))
    (e.injective.comp (EvenModels.componentEmbedding_injective s))
  exact d.symm.injective (by simp only [map_mul]; exact mul_comm _ _)

/-- No binary PSU₃ contains the component, for every actual Hermitian form. -/
theorem SimpleInput.not_even_unitary_three {n : ℕ} (hn : 0 < n) :
    ¬ ClassicalGroup.IsPSU S 3 (2 ^ n) := by
  rintro ⟨E, _, _, J, hcard, hconj, ⟨e⟩⟩
  have hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  let K := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  obtain ⟨d⟩ :=
    HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv
      J (2 ^ n) hcard hfixed
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup K) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Matrix.PSL3Two.not_injective_of_sylow_involutions_commute
    (HermitianForm.EvenTwoRank.rootSylow K rfl hn hcard hfixed)
    (HermitianForm.EvenTwoRank.rootSylow_involutions_commute K rfl hn hcard hfixed)
    ((e.trans d).toMonoidHom.comp (EvenModels.componentEmbedding s))
    ((e.trans d).injective.comp (EvenModels.componentEmbedding_injective s))

/-- Suzuki is excluded by its three-free order on the actual matrix carrier. -/
theorem SimpleInput.not_suzuki {m : ℕ} (hm : 1 ≤ m) :
    ¬ Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have h := EvenModels.three_dvd_card s
  rw [Nat.card_congr e.toEquiv] at h
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) h

/-- All three Bender alternatives in Theorem C are impossible. -/
theorem SimpleInput.not_bender : ¬ ClassificationModels.IsBenderModel S := by
  intro h
  cases h with
  | linear _ _ iso => exact s.not_even_linear_two iso
  | unitary _ hn iso => exact s.not_even_unitary_three (by omega) iso
  | suzuki _ hm iso => exact s.not_suzuki hm iso

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
