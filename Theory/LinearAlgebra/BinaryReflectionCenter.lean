module
public import Theory.GroupTheory.SolvableResidual
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Transvection.Basic
/-!
# Centers of irreducible binary groups normalized by a transvection

A central element with a nonzero fixed vector fixes the whole irreducible
module. If a rank-one map normalizes the group, its commutator with a central
element fixes the intersection of two hyperplanes. Above dimension two that
intersection is nonzero, so the two elements commute. The central element
then fixes the rank-one map's direction and is itself trivial.

A nondegenerate binary quadratic form has a nonsingular reflection. It
normalizes the full orthogonal solvable residual, giving centerlessness
whenever that residual acts irreducibly. This uses the source's irreducibility
and does not require orthogonal simplicity or a classification of its center.
Source application: Aschbacher--Smith G.10.15, printed p.363.
-/

public noncomputable section
open Subgroup Module
namespace BinaryReflectionCenter
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable (K : Subgroup (V ≃ₗ[ZMod 2] V))

private theorem central_eq_one_of_fixed
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ k∈K,∀ w∈W,k w∈W) → W=⊥ ∨ W=⊤)
    (z : K) (hz : z∈center K) (x : V) (hx : x≠0) (hfix : z.val x=x) : z=1 := by
  let W := (z.val.toLinearMap-LinearMap.id).ker
  have hmem (w : V) : w∈W ↔ z.val w=w := by
    change z.val w-w=0 ↔ _
    exact sub_eq_zero
  have hs : ∀ k∈K,∀ w∈W,k w∈W := by
    intro k hk w hw
    apply (hmem _).mpr
    have hh := congrArg (fun a : K => a.val w) ((mem_center_iff.mp hz) ⟨k,hk⟩)
    change k (z.val w)=z.val (k w) at hh
    rw [(hmem _).mp hw] at hh
    exact hh.symm
  have ht : W=⊤ := (hirr W hs).resolve_left (fun hb => hx (by
    have hm := (hmem x).mpr hfix
    rwa [hb,Submodule.mem_bot] at hm))
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  exact (hmem w).mp (ht ▸ Submodule.mem_top)
/-- A normalizing rank-one map kills the center of an irreducible binary
linear group in dimension greater than two. -/
theorem center_eq_bot_of_normalizing_transvection
    [FiniteDimensional (ZMod 2) V]
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ k∈K,∀ w∈W,k w∈W) → W=⊥ ∨ W=⊤)
    (hd : 2 < finrank (ZMod 2) V)
    (r : V ≃ₗ[ZMod 2] V) (hr : r∈normalizer (K : Set (V ≃ₗ[ZMod 2] V)))
    (v : V) (hv : v≠0) (φ : Module.Dual (ZMod 2) V) (hφ : φ≠0)
    (hrf : ∀ x,r x=x+φ x • v) : center K=⊥ := by
  apply bot_unique
  intro z hz
  apply mem_bot.mpr
  let θ := K.normalizerMonoidHom ⟨r,hr⟩
  let a := θ z*z⁻¹
  have ha : a∈center K := (center K).mul_mem
    (Subgroup.centerCongr θ ⟨z,hz⟩).property ((center K).inv_mem hz)
  let ψ := φ.prod (φ.comp z.val.toLinearMap)
  have hk : ψ.ker≠⊥ := by
    intro hk
    have hi : Function.Injective ψ := LinearMap.ker_eq_bot.mp hk
    have hb := LinearMap.finrank_le_finrank_of_injective hi
    have ht : finrank (ZMod 2) (ZMod 2 × ZMod 2)=2 := by simp
    rw [ht] at hb
    omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hxφ : φ x=0 := congrArg Prod.fst hx
  have hzxφ : φ (z.val x)=0 := congrArg Prod.snd hx
  have hrx : r x=x := by rw [hrf,hxφ,zero_smul,add_zero]
  have hrzx : r (z.val x)=z.val x := by rw [hrf,hzxφ,zero_smul,add_zero]
  have ha1 : a=1 := central_eq_one_of_fixed K hirr a ha (z.val x)
    (fun hh => hx0 (z.val.injective (hh.trans z.val.map_zero.symm))) (by
      change r (z.val (r.symm (z.val.symm (z.val x))))=z.val x
      rw [z.val.symm_apply_apply,← hrx,r.symm_apply_apply,hrzx,hrx])
  have hθ : θ z=z := mul_inv_eq_one.mp ha1
  have hc (y : V) : r (z.val y)=z.val (r y) := by
    have hh := congrArg (fun b : K => b.val (r y)) hθ
    change r (z.val (r.symm (r y)))=z.val (r y) at hh
    simpa only [r.symm_apply_apply] using hh
  obtain ⟨y,hy⟩ := Module.Dual.range_eq_top_of_ne_zero hφ ▸
    (show (1 : ZMod 2)∈(⊤ : Submodule (ZMod 2) (ZMod 2)) from trivial)
  have hvz : z.val v=v := by
    have hh := hc y
    rw [hrf,hrf,map_add,map_smul,hy,one_smul] at hh
    have he : φ (z.val y) • v=z.val v := add_left_cancel hh
    rcases (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) (φ (z.val y)) with h|h
    · rw [h,zero_smul] at he
      exact (hv (z.val.injective (he.symm.trans z.val.map_zero.symm))).elim
    · simpa only [h,one_smul] using he.symm
  exact central_eq_one_of_fixed K hirr z hz v hv hvz

/-- The full orthogonal residual has trivial center as soon as its literal
action is irreducible in dimension greater than two. -/
theorem center_orthogonal_residual_eq_bot
    [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V) (hnd : q.polarBilin.Nondegenerate)
    (hd : 2 < finrank (ZMod 2) V)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ k∈(solvableResidual q.isometrySubgroup).map q.isometrySubgroup.subtype,
        ∀ w∈W,k w∈W) → W=⊥ ∨ W=⊤) :
    center ((solvableResidual q.isometrySubgroup).map q.isometrySubgroup.subtype)=⊥ := by
  let D := q.isometrySubgroup
  let N := (solvableResidual D).map D.subtype
  have hn : D ≤ normalizer (N : Set (V ≃ₗ[ZMod 2] V)) := by
    have hh := (solvableResidual D).le_normalizer_map D.subtype
    rw [Subgroup.normalizer_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh
  obtain ⟨v,hv⟩ : ∃ v : V,q v≠0 := by
    by_contra! hz
    have hall (x : V) : x=0 := hnd.1 x (fun y => by
      change q (x+y)-q x-q y=0
      rw [hz,hz,hz,sub_self,sub_zero])
    let : Subsingleton V := ⟨fun x y => (hall x).trans (hall y).symm⟩
    have hh : finrank (ZMod 2) V=0 := Module.finrank_zero_of_subsingleton
    omega
  have hv1 : q v=1 :=
    (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) (q v) |>.resolve_left hv
  have hv0 : v≠0 := fun hh => hv (hh ▸ q.map_zero)
  have hself : q.polarBilin v v=0 := by
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_self]
    rw [two_smul]
    exact (show ∀ c : ZMod 2,c+c=0 from by decide) _
  let r := LinearEquiv.transvection hself
  have hr (x : V) : r x=x+q.polarBilin v x • v := rfl
  have hswap (x y : V) : q.polarBilin x y=q.polarBilin y x :=
    QuadraticMap.polar_comm q x y
  have hD : r∈D := by
    apply (QuadraticMap.mem_isometrySubgroup q r).mpr
    intro x
    rw [hr,QuadraticMap.map_add q,q.map_smul]
    simp only [smul_eq_mul,← pow_two]
    change q x + (q.polarBilin v x)^2*q v+
      q.polarBilin x (q.polarBilin v x • v)=q x
    rw [map_smul,smul_eq_mul,hswap x v,hv1,mul_one]
    have hbit : ∀ a b : ZMod 2,a+b^2+b*b=a := by decide
    exact hbit _ _
  apply center_eq_bot_of_normalizing_transvection N hirr hd r (hn hD) v hv0
    (q.polarBilin v) (fun hh => hv0 (hnd.1 v (fun y => LinearMap.congr_fun hh y))) hr

end BinaryReflectionCenter
