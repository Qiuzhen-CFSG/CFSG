module
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Separating a moved conjugate of a dihedral-eight factor

A dihedral-eight subgroup with a central involution moved outside it by a
normalizing conjugator has a disjoint right conjugate. The two normal factors
then commute, and an order-sixty-four ambient subgroup is their direct product.
Source: Aschbacher–Smith, 2.4.36(1), printed pp.549–550,
combined manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory
open Subgroup
open scoped commutatorElement

/-- A conjugating element exchanging the marked centers separates two
normal dihedral-eight factors in a group of order sixty-four. -/
theorem dihedral_conjugate_pair_of_moved_center
    {G : Type*} [Group G] [Finite G]
    (R D : Subgroup G) (hDR : D ≤ R) (hRD : R ≤ normalizer (D:Set G))
    (eD : D ≃* DihedralGroup 4) (hRcard : Nat.card R=64)
    (t : G) (htR : t ∈ normalizer (R:Set G)) (htD : t^2 ∈ normalizer (D:Set G))
    (z : G) (hzD : z ∈ D) (hz1 : z ≠1) (hzC : z ∈ centralizer (D:Set G))
    (hmoved : t*z*t⁻¹ ∉ D) :
    let E := D.map (MulAut.conj t).toMonoidHom
    D ⊔ E = R ∧ Disjoint D E ∧ D ≤ centralizer (E:Set G) := by
  let E := D.map (MulAut.conj t).toMonoidHom
  have hRmap : R.map (MulAut.conj t).toMonoidHom=R := mem_normalizer_iff_map_conj_eq.mp htR
  have hER : E ≤ R := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hDR
    rwa [hRmap] at hh
  have hRE : R ≤ normalizer (E:Set G) := by
    rw [show normalizer (E:Set G) = (normalizer (D:Set G)).map (MulAut.conj t).toMonoidHom
      from (map_equiv_normalizer_eq D (MulAut.conj t)).symm]
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hRD
    rwa [hRmap] at hh
  have hDc : Nat.card D=8 := by rw [Nat.card_congr eD.toEquiv,DihedralGroup.nat_card]
  have hZc : Nat.card (center D)=2 := DihedralGroup.center_card_of_equiv (n:=2) (by decide) eD
  have hdp : IsPGroup 2 D := IsPGroup.of_card (show Nat.card D=2^3 by omega)
  have hd : Disjoint D E := by
    apply disjoint_def.mpr
    intro x hxD hxE
    by_contra hx1
    let J := E.subgroupOf D
    let : J.Normal := normal_subgroupOf_of_le_normalizer (hDR.trans hRE)
    have hJ : J ≠ ⊥ := by
      intro he
      have hx : (⟨x,hxD⟩ : D) ∈ J := hxE
      rw [he,mem_bot] at hx
      exact hx1 (congrArg Subtype.val hx)
    have hmeet := center_inf_ne_bot_of_normal hdp J hJ
    obtain ⟨y,hy1⟩ := ne_bot_iff_exists_ne_one.mp hmeet
    let zD : D := ⟨z,hzD⟩
    have hzDc : zD ∈ center D := by
      rw [mem_center_iff]
      intro a
      exact Subtype.ext (hzC a a.property)
    let zZ : center D := ⟨zD,hzDc⟩
    let yZ : center D := ⟨y.val,y.property.1⟩
    have hzZ1 : zZ≠1 := fun he => hz1 (congrArg (fun a : center D => ((a:D):G)) he)
    have hyZ1 : yZ≠1 := by
      intro he
      have hh : y.val=1 := congrArg (fun a : center D => (a:D)) he
      exact hy1 (Subtype.ext hh)
    obtain ⟨w,hw,huniq⟩ := (Nat.card_eq_two_iff' (1:center D)).mp hZc
    have hzy : zZ=yZ := (huniq zZ hzZ1).trans (huniq yZ hyZ1).symm
    have hzE : z ∈ E := by
      have hyE : (y.val:G) ∈ E := y.property.2
      have he : z=(y.val:G) := congrArg (fun a : center D => ((a:D):G)) hzy
      rw [he]
      exact hyE
    have hh : E.map (MulAut.conj t).toMonoidHom=D := by
      change (D.map _).map _=D
      rw [map_map]
      have he : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          (MulAut.conj (t^2)).toMonoidHom := by
        ext a
        simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,pow_two,mul_inv_rev]
        group
      rw [he]
      exact mem_normalizer_iff_map_conj_eq.mp htD
    exact hmoved (hh ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom hzE)
  have hc : D ≤ centralizer (E:Set G) := by
    rw [←commutator_eq_bot_iff_le_centralizer]
    apply bot_unique
    apply le_trans (le_inf
      (le_normalizer_iff_commutator_le_left.mp (hER.trans hRD))
      (le_normalizer_iff_commutator_le_right.mp (hDR.trans hRE)))
    exact hd.eq_bot.le
  have hEc : Nat.card E=8 := (card_map_of_injective (MulAut.conj t).injective).trans hDc
  have hgen : D ⊔ E=R := eq_of_le_of_card_ge (sup_le hDR hER) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D E (hER.trans hRD) hd,hRcard,hDc,hEc])
  exact ⟨hgen,hd,hc⟩
end Theory.GroupTheory
