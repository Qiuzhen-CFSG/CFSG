module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SmallModels
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Excluding the solvable-kernel rows of A.3.12

A binary simple quasisimple group has no nontrivial solvable normal subgroup.
Each displayed elementary, extraspecial, homocyclic, or cyclic-extraspecial
kernel is solvable and nontrivial, so these extension rows cannot occur.
The quotient model is unrestricted and no splitting is assumed.
Source: Aschbacher–Smith A.3.12(10,12–14,16–19), pp.47–48, in C.5.13.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels
universe u
variable {B : Type u} [Group B] [Finite B] [IsQuasisimple B] {n : ℕ}

omit [Finite B] in
private theorem solvable_normal_eq_bot (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) (N : Subgroup B) [N.Normal]
    (hs : Group.IsSolvable N) : N = ⊥ := by
  let : IsSimpleGroup B := binary_simple hn hB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N inferInstance with he | he
  · exact he
  · let : Group.IsSolvable N := hs
    let e : N ≃* B := (MulEquiv.subgroupCongr he).trans topEquiv
    have hsol : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact (Group.IsPerfect.not_isSolvable B hsol).elim

omit [Finite B] in
theorem binary_no_elementary_extension (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) {p r : ℕ}
    (hp : 1 < p) (hr : 0 < r) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (ElementaryModel p r) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = p^r := by
    rw [Nat.card_congr e.toEquiv]
    let : NeZero p := ⟨by omega⟩
    simp
  rw [solvable_normal_eq_bot hn hB N hs,card_bot] at hc
  exact (Nat.one_lt_pow (by omega) hp).ne hc

theorem binary_no_extraspecial_extension (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) {p r : ℕ}
    [Fact p.Prime] (ψ : GroupClass.{u}) : ¬ HasExtension B (ExtraspecialModel p r) ψ := by
  rintro ⟨N,_,⟨hex,hcard⟩,_⟩
  let : IsExtraspecial p N := hex
  let : Group.IsNilpotent N := (IsExtraspecial.isPGroup p N).isNilpotent
  have hs : Group.IsSolvable N := inferInstance
  rw [solvable_normal_eq_bot hn hB N hs,card_bot] at hcard
  exact (Nat.one_lt_pow (by omega) (Fact.out : p.Prime).one_lt).ne hcard

omit [Finite B] in
theorem binary_no_homocyclic_four_extension (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (fun X _ => Nonempty (X ≃* Multiplicative (Fin 3 → ZMod 4))) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = 64 := by rw [Nat.card_congr e.toEquiv]; norm_num
  rw [solvable_normal_eq_bot hn hB N hs,card_bot] at hc
  omega

theorem binary_no_cyclic_extraspecial_extension (hn : 1 < n)
    (hB : ClassicalGroup.IsPSL B 2 (2^n)) (r : ℕ) (ψ : GroupClass.{u}) :
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
  rw [hcardC,solvable_normal_eq_bot hn hB N hs,card_bot] at hc
  omega
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
