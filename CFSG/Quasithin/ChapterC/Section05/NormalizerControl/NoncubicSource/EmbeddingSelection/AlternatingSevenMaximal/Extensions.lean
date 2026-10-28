module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Basic
public import Theory.ElementaryAbelian.Extraspecial
/-!
# The solvable-kernel A.3.12 rows exclude A₇

A₇ is simple and perfect, so each displayed nontrivial solvable normal
kernel is impossible. The quotient model is unrestricted and no splitting
is imposed.
Source: Aschbacher–Smith A.3.12 and C.5.12, pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
open Chapter1.Section02.LocalModels
universe u
variable {B : Type u} [Group B] [Finite B]
omit [Finite B] in
theorem no_elementary_extension (hB : IsAlternating B 7) {p r : ℕ}
    (hp : 1 < p) (hr : 0 < r) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (ElementaryModel p r) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = p^r := by
    rw [Nat.card_congr e.toEquiv]
    let : NeZero p := ⟨by omega⟩
    simp
  rw [solvable_normal_eq_bot hB N hs,card_bot] at hc
  exact (Nat.one_lt_pow (by omega) hp).ne hc

theorem no_extraspecial_extension (hB : IsAlternating B 7) {p r : ℕ}
    [Fact p.Prime] (ψ : GroupClass.{u}) : ¬ HasExtension B (ExtraspecialModel p r) ψ := by
  rintro ⟨N,_,⟨hex,hcard⟩,_⟩
  let : IsExtraspecial p N := hex
  let : Group.IsNilpotent N := (IsExtraspecial.isPGroup p N).isNilpotent
  have hs : Group.IsSolvable N := inferInstance
  rw [solvable_normal_eq_bot hB N hs,card_bot] at hcard
  exact (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt).ne hcard

omit [Finite B] in
theorem no_homocyclic_four_extension (hB : IsAlternating B 7) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (fun X _ => Nonempty (X ≃* Multiplicative (Fin 3 → ZMod 4))) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = 64 := by rw [Nat.card_congr e.toEquiv]; norm_num
  rw [solvable_normal_eq_bot hB N hs,card_bot] at hc
  omega

theorem no_cyclic_extraspecial_extension (hB : IsAlternating B 7) (r : ℕ) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (CyclicFourCentralProduct r) ψ := by
  rintro ⟨N,_,⟨C,E,⟨eC⟩,hE,hgen,hcomm,_⟩,_⟩
  have hcardC : Nat.card C = 4 := by rw [Nat.card_congr eC.toEquiv]; simp
  have hpC : IsPGroup 2 C := IsPGroup.of_card (n := 2) (by simpa using hcardC)
  let : IsExtraspecial 2 E := hE.1
  have hpE := IsExtraspecial.isPGroup 2 E
  have hCN : C ≤ normalizer (E : Set N) :=
    (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (Subgroup.centralizer_le_normalizer _)
  have hp : IsPGroup 2 N :=
    (hpC.to_sup_of_normal_right' hpE hCN).of_equiv
      ((MulEquiv.subgroupCongr hgen).trans topEquiv)
  let : Group.IsNilpotent N := hp.isNilpotent
  have hs : Group.IsSolvable N := inferInstance
  have hc := C.card_le_card_group
  rw [hcardC,solvable_normal_eq_bot hB N hs,card_bot] at hc
  omega
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection.AlternatingSevenMaximal
