module
public import Theory.SpecificGroups.PSL2.PrimeFourSolvableBound
public import Theory.SpecificGroups.PSL2.TwentyFiveCartanNormalizer
import all Theory.SpecificGroups.PSL2.PrimeFourSolvable

/-!
# Full odd actions in solvable PSL₂(25) extensions

A solvable subgroup containing an actual A₄ has order dividing twenty-four,
by Dickson's classification. The outer automorphism quotient is a two-group,
so an odd automorphism subgroup in such a solvable extension has order at
most three. This controls the whole original Cartan intersection in the
PSL₂(25) row, without first selecting an escaping cubic.

The internal import reuses the elementary A₄ embedding obstructions while
preserving their public boundary. Source: Huppert II.8.27 and
Aschbacher--Smith 5.1.13, printed p.636.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace Theory.PSL2.TwentyFive
open PrimeFourSolvable
local notation "A4" => alternatingGroup (Fin 4)
/-- A solvable subgroup of PSL₂(25) containing A₄ has order dividing twenty-four. -/
theorem card_dvd_twentyFour_of_alternating_four
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25)
    (H : Subgroup (PSL2MatrixGroup F)) [_root_.Group.IsSolvable H]
    (f : A4 →* H) (hi : Function.Injective f) : Nat.card H ∣ 24 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ho : Odd (5 : ℕ) := by decide
  have hcardF : Nat.card F = 5 ^ 2 := hF
  have h4 : 4 ∣ Nat.card H := by
    have hd := card_dvd_of_injective f hi
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact (by decide : 4 ∣ 12).trans hd
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification
      hcardF H with hEl | hCy | hDi | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 5 H).exists_card_eq
    exact ((ha ▸ ho.pow).not_two_dvd_nat ((by decide : 2 ∣ 4).trans h4)).elim
  · let : IsCyclic H := hCy.choose_spec.2.2
    exact (a4_not_cyclic (isCyclic_of_injective f hi)).elim
  · obtain ⟨_,_,_,⟨e⟩⟩ := hDi
    exact (no_dihedral_embedding (e.toMonoidHom.comp f) (e.injective.comp hi)).elim
  · obtain ⟨_,⟨e⟩⟩ := hA4
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hS4
    rw [Nat.card_congr e.toEquiv,Nat.card_perm]
    norm_num [Nat.factorial]
  · obtain ⟨_,⟨e⟩⟩ := hA5
    let : _root_.Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact False.elim <| _root_.Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,t,_,_,N,C,hN,_,hcN,hC,_,hd,hs⟩ := hAff
    let := hN
    let := hC
    exact (no_odd_cyclic_embedding N C (by rw [hcN]; exact ho.pow) hd hs f hi).elim
  · obtain ⟨a,ha,_,⟨e⟩⟩ := hPSL
    have hc : 3 < Nat.card (GaloisField 5 a) := by
      rw [GaloisField.card 5 a ha]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 5) (Nat.one_le_iff_ne_zero.mpr ha)
      norm_num at hh
      omega
    let : _root_.Group.IsPerfect (PSL2MatrixGroup (GaloisField 5 a)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ hc
    exact False.elim <| _root_.Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField 5 a))
      (_root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,ha,_,⟨e⟩⟩ := hPGL
    have hc : 3 < Nat.card (GaloisField 5 a) := by
      rw [GaloisField.card 5 a ha]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 5) (Nat.one_le_iff_ne_zero.mpr ha)
      norm_num at hh
      omega
    let : _root_.Group.IsPerfect (PSL2MatrixGroup (GaloisField 5 a)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ hc
    let : _root_.Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 5 a)) :=
      _root_.Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact False.elim <| _root_.Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField 5 a))
      (_root_.Group.isSolvable_of_isSolvable_injective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := GaloisField 5 a)))



/-- An odd group of automorphisms in a solvable group containing an inner A₄
has order at most three. -/
theorem odd_aut_card_le_three
    {X : Type*} [_root_.Group X] [Finite X]
    {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 25)
    (e : X ≃* PSL2MatrixGroup F)
    (J E : Subgroup (MulAut X)) [_root_.Group.IsSolvable J]
    (hE : E ≤ J) (hodd : Odd (Nat.card E))
    (a : A4 →* X) (ha : Function.Injective a)
    (hJ : ∀ x, MulAut.conj (a x) ∈ J) : Nat.card E ≤ 3 := by
  have hz : center X = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (PSL2MatrixGroup F) at hh
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hout : IsPGroup 2 (MulAut.Outer X) :=
    (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (by decide : Nat.Prime 5) (by decide : Odd 5) (by decide : 2 ≤ 2)
      (show Nat.card F = 5 ^ 2 from hF)).of_equiv (MulAut.outerCongr e).symm
  let i : X →* MulAut X := MulAut.conj
  have hi : Function.Injective i := conj_injective_of_center_eq_bot hz
  have hEin : E ≤ MulAut.innerSubgroup X :=
    OddHall.odd_subgroup_le _ E hout hodd
  let ec : X ≃* MulAut.innerSubgroup X := MonoidHom.ofInjective hi
  let b : E →* MulAut.innerSubgroup X := E.subtype.codRestrict _ (fun x => hEin x.property)
  let g := ec.symm.toMonoidHom.comp b
  have hg (x : E) : i (g x) = x := congrArg Subtype.val (ec.apply_symm_apply (b x))
  have hgi : Function.Injective g := by
    intro x y he
    exact Subtype.ext ((hg x).symm.trans ((congrArg i he).trans (hg y)))
  let M := J.comap i
  let : _root_.Group.IsSolvable M := _root_.Group.isSolvable_of_isSolvable_injective
    (f := i.subgroupComap J) (fun x y he => Subtype.ext (hi (congrArg Subtype.val he)))
  have hM (x : A4) : a x ∈ M := hJ x
  have hgm (x : E) : g x ∈ M := by
    change i (g x) ∈ J
    rw [hg]
    exact hE x.property
  have hd : Nat.card E ∣ Nat.card M := card_dvd_of_injective
    (g.codRestrict M hgm) (fun x y he => hgi (congrArg Subtype.val he))
  let eM := M.equivMapOfInjective e.toMonoidHom e.injective
  let : _root_.Group.IsSolvable (M.map e.toMonoidHom) :=
    _root_.Group.isSolvable_of_surjective (f := eM.toMonoidHom) eM.surjective
  have hc := card_dvd_twentyFour_of_alternating_four hF (M.map e.toMonoidHom)
    (eM.toMonoidHom.comp (a.codRestrict M hM))
    (eM.injective.comp (fun _ _ he => ha (congrArg Subtype.val he)))
  rw [card_map_of_injective e.injective] at hc
  have hd3 : Nat.card E ∣ 3 := (hodd.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left
    (show Nat.card E ∣ 2^3 * 3 from hd.trans hc)
  exact Nat.le_of_dvd (by decide) hd3
end Theory.PSL2.TwentyFive
