module

public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Recognition
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Geometry
public import Theory.GroupAction.SimpleCosets
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Two conjugates of a noncyclic binary root subgroup

The explicit internal Weyl element produces a subgroup with trivial two-core.
Its intersection with the original root group is Sylow. Binary Dickson
recognition identifies the subgroup with SL₂(2^k), where k > 1 divides the
ambient degree. Inner conjugacy aligns its Sylow with the standard upper root
group, hence aligns the actual ambient Borel intersection as well. Simplicity
makes that Borel core-free.

The witness retains the original subgroup, original generator V and internal
conjugator. Source: Aschbacher–Smith E.2.7, printed p.218, linear Bender branch.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.TwoConjugateWitness

structure Witness {G : Type*} [Group G] (S M V : Subgroup G) (n : ℕ) where
  subgroup : Subgroup G
  le : V ≤ subgroup
  conjugator : subgroup
  outside : (conjugator : G) ∉ M
  generate : V.subgroupOf subgroup ⊔
    (V.subgroupOf subgroup).map (MulAut.conj conjugator).toMonoidHom = ⊤
  sylow : Sylow 2 subgroup
  sylow_eq : (sylow : Subgroup subgroup) = S.subgroupOf subgroup
  degree : ℕ
  degree_gt_one : 1 < degree
  degree_dvd : degree ∣ n
  model : subgroup ≃* SL(2,GaloisField 2 degree)
  sylow_model : (sylow : Subgroup subgroup).map model.toMonoidHom =
    upperUnipotent (GaloisField 2 degree)
  borel_model : (M.subgroupOf subgroup).map model.toMonoidHom =
    rankOneBorel (GaloisField 2 degree)
  corefree : (M.subgroupOf subgroup).normalCore = ⊥

theorem pair_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

theorem exists_upper {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (V : Subgroup SL(2,F))
    (hV : V ≤ upperUnipotent F) (hVc : 4 ≤ Nat.card V) :
    Nonempty (Witness (upperUnipotent F) (rankOneBorel F) V n) := by
  have hn : V ≠ ⊥ := by intro h; simp [h] at hVc
  obtain ⟨v,hv,hv1⟩ := V.bot_or_exists_ne_one.resolve_left hn
  obtain ⟨a,rfl⟩ := (mem_upperUnipotent F v).mp (hV hv)
  have ha : a ≠ 0 := by intro h; exact hv1 (by simp [h,transvection_coeff_zero])
  let w := rootWeyl a ha
  let I := V ⊔ V.map (MulAut.conj w).toMonoidHom
  have hVI : V ≤ I := le_sup_left
  have hw : w ∈ I := rootWeyl_mem_join ha hv
  let g : I := ⟨w,hw⟩
  let P := intersectionSylow I ha (hVI hv)
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [pair_map, map_subgroupOf_eq_of_le hVI, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hPc : 4 ≤ Nat.card P := by
    let f : V → P := fun x => ⟨⟨x,hVI x.property⟩,hV x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : P => ((z : I) : SL(2,F))) h)
    exact hVc.trans (Nat.card_le_card_of_injective f hf)
  obtain ⟨k,hk,hkn,⟨e⟩⟩ := sl_subgroup_recognition hF I (rootWeyl_join_twoCore hV ha hv) P hPc
  let E := GaloisField 2 k
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨z,hz⟩ := MulAction.exists_smul_eq SL(2,E) Q (upperUnipotentSylow E 2)
  let d := e.trans (MulAut.conj z)
  have hmodel : (P : Subgroup I).map d.toMonoidHom = upperUnipotent E := by
    rw [show d.toMonoidHom = (MulAut.conj z).toMonoidHom.comp e.toMonoidHom from rfl,
      ← Subgroup.map_map]
    exact congrArg (fun R : Sylow 2 SL(2,E) => R.toSubgroup) hz
  have hB : ((rankOneBorel F).subgroupOf I).map d.toMonoidHom = rankOneBorel E := by
    rw [← intersection_normalizer I ha (hVI hv)]
    change (normalizer ((P : Subgroup I) : Set I)).map d.toMonoidHom = rankOneBorel E
    have hn := map_equiv_normalizer_eq (P : Subgroup I) d
    rw [hn, hmodel]
  have hEc : 4 ≤ Nat.card E := by
    rw [GaloisField.card 2 k (by omega)]
    exact (show 2^2 ≤ 2^k from Nat.pow_le_pow_right (by decide) (by omega))
  let : IsSimpleGroup PSL(2,E) := ProjectiveSpecialLinearGroup.rank_two_simple hEc
  let : IsSimpleGroup I := (d.trans (slEquivPSL E)).isSimpleGroup
  have hcore : ((rankOneBorel F).subgroupOf I).normalCore = ⊥ := by
    apply normalCore_eq_bot_of_simple
    intro h
    have hh : g ∈ (rankOneBorel F).subgroupOf I := h.symm ▸ mem_top g
    exact rootWeyl_not_mem_borel a ha hh
  exact ⟨⟨I,hVI,g,rootWeyl_not_mem_borel a ha,hgen,P,rfl,k,hk,hkn,d,hmodel,hB,hcore⟩⟩


end Matrix.SpecialLinearGroup.TwoConjugateWitness
