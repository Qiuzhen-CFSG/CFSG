module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Extensions
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import BenderSuzuki.External.Huppert.II.theorem_6_14
/-!
# Distinguishing the small central cover in the A.3.12 list

SL2(5) has order 120 and center of order two. Every solvable normal
subgroup of this quasisimple group is central, so each displayed larger
solvable kernel in the embedding list is impossible. The model-order and
center comparisons below retain the actual finite-field SL2 marking.
Source: Aschbacher--Smith A.3.12, pp.47--48, as used in C.5.12 p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {B : Type u} [Group B]

theorem sl2_five_card (hB : IsSL B 2 5) : Nat.card B = 120 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hB
  rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF]
  norm_num

theorem sl2_five_center_card (hB : IsSL B 2 5) : Nat.card (center B) = 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hB
  rw [Nat.card_congr (centerCongr e).toEquiv,Atlas.ExceptionalSupport.card_sl_center,hF]
  decide

variable [Finite B] [IsQuasisimple B]

theorem sl2_five_solvable_normal_card (hB : IsSL B 2 5)
    (N : Subgroup B) [N.Normal] (hs : Group.IsSolvable N) : Nat.card N ≤ 2 := by
  have hn : N ≤ center B := (le_solvableRadical N inferInstance hs).trans
    IsQuasisimple.solvableRadical_le_center
  exact (Nat.card_le_card_of_injective (inclusion hn) (inclusion_injective hn)).trans_eq
    (sl2_five_center_card hB)

theorem sl2_five_no_elementary_extension (hB : IsSL B 2 5) {p r : ℕ}
    (hp : 1 < p) (hr : 2 ≤ r) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (ElementaryModel p r) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = p^r := by
    rw [Nat.card_congr e.toEquiv]
    let : NeZero p := ⟨by omega⟩
    simp
  have hb := sl2_five_solvable_normal_card hB N hs
  have hlo : 4 ≤ p^r := (Nat.pow_le_pow_left (by omega : 2≤p) 2).trans
    (Nat.pow_le_pow_right (by omega : 0<p) hr)
  omega

theorem sl2_five_no_extraspecial_extension (hB : IsSL B 2 5) {r : ℕ}
    (hr : 1 ≤ r) (ψ : GroupClass.{u}) : ¬ HasExtension B (ExtraspecialModel 2 r) ψ := by
  rintro ⟨N,_,⟨hex,hcard⟩,_⟩
  let : IsExtraspecial 2 N := hex
  let : Group.IsNilpotent N := (IsExtraspecial.isPGroup 2 N).isNilpotent
  have hb := sl2_five_solvable_normal_card hB N inferInstance
  have hlo : 8 ≤ 2^(1+2*r) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 3≤1+2*r)
  omega

theorem sl2_five_no_homocyclic_four_extension (hB : IsSL B 2 5) (ψ : GroupClass.{u}) :
    ¬ HasExtension B (fun X _ => Nonempty (X ≃* Multiplicative (Fin 3 → ZMod 4))) ψ := by
  rintro ⟨N,_,⟨e⟩,_⟩
  have hs : Group.IsSolvable N := Group.isSolvable_of_comm (fun a b => e.injective (by
    simp only [map_mul,mul_comm]))
  have hc : Nat.card N = 64 := by rw [Nat.card_congr e.toEquiv]; norm_num
  have hb := sl2_five_solvable_normal_card hB N hs
  omega

theorem sl2_five_no_cyclic_extraspecial_extension (hB : IsSL B 2 5)
    (r : ℕ) (ψ : GroupClass.{u}) : ¬ HasExtension B (CyclicFourCentralProduct r) ψ := by
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
  have hb := sl2_five_solvable_normal_card hB N inferInstance
  have hc := C.card_le_card_group
  omega

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_not_alternating (hB : IsSL B 2 5) (n : ℕ) (hn : n=5 ∨ n=6) :
    ¬ IsAlternating B n := by
  rintro ⟨e⟩
  have hc := sl2_five_card hB
  rw [Nat.card_congr e.toEquiv] at hc
  rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] at hc <;> norm_num at hc

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_not_three_cover (hB : IsSL B 2 5) (n : ℕ) :
    ¬ IsAlternatingCover B n := by
  rintro ⟨_,⟨e⟩,_⟩
  have hc := sl2_five_center_card hB
  rw [Nat.card_congr e.toEquiv] at hc
  norm_num at hc

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_not_psl2 (hB : IsSL B 2 5) (q : ℕ) :
    ¬ ClassicalGroup.IsPSL B 2 q := by
  rintro ⟨F,_,_,_,⟨e⟩⟩
  have hz := GorensteinWalter.center_eq_bot_of_mulEquiv e (GorensteinWalter.psl2_center_eq_bot F)
  have hc := sl2_five_center_card hB
  rw [hz,card_bot] at hc
  omega

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_not_psl3 (hB : IsSL B 2 5) (q : ℕ) (hq : q=2 ∨ q=4) :
    ¬ ClassicalGroup.IsPSL B 3 q := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  rw [← Nat.card_congr e.toEquiv,sl2_five_card hB,hF] at hc
  rcases hq with rfl | rfl <;> norm_num [Fin.prod_univ_succ] at hc

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_not_mathieu_twenty_two (hB : IsSL B 2 5) :
    ¬ Nonempty (B ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨e⟩
  have hc := sl2_five_card hB
  rw [Nat.card_congr e.toEquiv,Sporadic.Mathieu.m22_order] at hc
  omega

omit [IsQuasisimple B] [Finite B] in
theorem sl2_five_parameter (hB : IsSL B 2 5) {p : ℕ} (hp : 3<p) (hm : IsSL B 2 p) : p=5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc := sl2_five_card hB
  rw [Nat.card_congr e.toEquiv,BenderSuzuki.External.huppert614_card_specialLinearGroup,hF] at hc
  have hp6 : p<6 := by
    by_contra h
    have hp' : 6≤p := by omega
    have hp2 : 36≤p^2 := by nlinarith
    have hp3 : 35≤p^2-1 := by omega
    nlinarith
  interval_cases p
  · norm_num at hc
  · rfl

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
