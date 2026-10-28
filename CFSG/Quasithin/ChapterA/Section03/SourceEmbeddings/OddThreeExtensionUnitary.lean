module

public import Theory.SpecificGroups.SU3.DefiningSylowProducts.Model
public import Theory.SpecificGroups.SU3.PrimeCentralKernel
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models

/-!
# Full-Sylow exclusion of the odd unitary extension branch

An elementary subgroup of order q² normalized by the original full Sylow
would permute with that Sylow. The actual PSU₃ defining-Sylow product theorem
excludes it. For SU₃ the central kernel has order dividing three; q > 3
makes projectivization injective on the q-subgroup, preserving its exact size.

Source: Aschbacher--Smith A.3.21 and A.3.12(10), pp.47,55--56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open BenderSuzuki.MatrixGroups
open Chapter1.Section02.LocalModels

theorem not_psu_of_normalized_prime_square
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (ho : Odd q) (hq : 3 < q) (S : Sylow 2 G) (U : Subgroup G)
    (hU : Nat.card U = q^2) (hSU : (S : Subgroup G) ≤ normalizer (U : Set G)) :
    ¬ ClassicalGroup.IsPSU G 3 q := by
  rintro ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
  let V := U.map e.toMonoidHom
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hVP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (V : Set _) :=
    (map_mono hSU).trans (U.le_normalizer_map e.toMonoidHom)
  exact HermitianForm.DefiningSylowProducts.not_permuting J q Fact.out ho hq hcard hconj P V
    (Or.inl ((card_map_of_injective e.injective).trans hU))
    (set_mul_normalizer_comm (P : Set _) V hVP).symm

theorem not_su_of_normalized_prime_square
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (ho : Odd q) (hq : 3 < q) (S : Sylow 2 G) (U : Subgroup G)
    (hU : Nat.card U = q^2) (hSU : (S : Subgroup G) ≤ normalizer (U : Set G)) :
    ¬ IsSU G 3 q := by
  rintro ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
  let f := J.specialToProjective.comp e.toMonoidHom
  have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective f hf
  let P := S.mapSurjective (f := f) hf
  let V := U.map f
  have hc : Nat.Coprime q (Nat.card f.ker) := by
    let i : f.ker →* J.specialToProjective.ker :=
      (e.toMonoidHom.comp f.ker.subtype).codRestrict _ (fun x => x.property)
    have hi : Function.Injective i := fun x y hh =>
      Subtype.ext (e.injective (congrArg Subtype.val hh))
    exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 3) hq)).of_dvd_right
        ((card_dvd_of_injective i hi).trans J.card_specialToProjective_ker_dvd_three)
  have hUp : IsPGroup q U := IsPGroup.of_card hU
  have hi : Function.Injective (f.comp U.subtype) :=
    injective_comp_subtype_of_coprime_ker f hc U hUp
  have hV : Nat.card V = q^2 := by
    have hh := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm.trans hU
    simpa only [MonoidHom.range_comp,range_subtype] using hh
  have hVP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ≤ normalizer (V : Set _) :=
    (map_mono hSU).trans (U.le_normalizer_map f)
  exact HermitianForm.DefiningSylowProducts.not_permuting J q Fact.out ho hq hcard hconj P V
    (Or.inl hV) (set_mul_normalizer_comm (P : Set _) V hVP).symm

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
