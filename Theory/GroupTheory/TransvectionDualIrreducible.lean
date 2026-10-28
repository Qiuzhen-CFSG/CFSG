module
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# Irreducibility on the other side of a full commutator pairing

An invariant subgroup of a transvection group has an invariant annihilator
in the original section. Irreducibility makes that annihilator either the
central line or the entire section. Finite-dimensional duality then makes
the subgroup either the full action kernel or the entire transvection group.
Both the central denominator and the full action kernel are retained.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G]

/-- A separating binary commutator pairing transfers irreducibility across
its two actual quotient maps, without choosing compatible model coordinates. -/
theorem transvection_dual_interval
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (W X K R : Subgroup G) (z : G) (hz : z ≠ 1)
    (qW : W →* Multiplicative M) (hqW : Function.Surjective qW)
    (hkerW : qW.ker = (zpowers z).subgroupOf W)
    (qX : X →* Multiplicative (Module.Dual (ZMod 2) M))
    (hkerX : qX.ker = K.subgroupOf X)
    (hpair : ∀ (x : X) (w : W), ⁅(x : G),(w : G)⁆ =
      z ^ ((qX x).toAdd (qW w).toAdd).val)
    (hZW : zpowers z ≤ W) (hXZ : X ≤ centralizer ({z} : Set G))
    (hRW : R ≤ normalizer (W : Set G))
    (hirr : ∀ A : Subgroup G, zpowers z ≤ A → A ≤ W →
      R ≤ normalizer (A : Set G) → A = zpowers z ∨ A = W)
    (Y : Subgroup G) (hKY : K ≤ Y) (hYX : Y ≤ X)
    (hRY : R ≤ normalizer (Y : Set G)) : Y = K ∨ Y = X := by
  have hzpow (c : ZMod 2) : z^c.val = 1 ↔ c = 0 := by
    fin_cases c <;> simp [hz,ZMod.val_one_eq_one_mod]
  have hp (x : X) (w : W) :
      (qX x).toAdd (qW w).toAdd = 0 ↔ (x : G)*(w : G)=(w : G)*(x : G) := by
    rw [←commutatorElement_eq_one_iff_mul_comm,hpair,hzpow]
  let A := W ⊓ centralizer (Y : Set G)
  have hZA : zpowers z ≤ A := le_inf hZW (zpowers_le.mpr (by
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hXZ (hYX hy))))
  have hRA : R ≤ normalizer (A : Set G) :=
    (le_inf hRW (hRY.trans (normalizer_le_normalizer_centralizer Y))).trans
      inf_normalizer_le_normalizer_inf
  rcases hirr A hZA inf_le_left hRA with hAz | hAW
  · right
    let P : Submodule (ZMod 2) (Module.Dual (ZMod 2) M) :=
      AddSubgroup.toZModSubmodule 2 ((Y.subgroupOf X).map qX).toAddSubgroup'
    have hPbot : P.dualCoannihilator = ⊥ := by
      apply bot_unique
      intro v hv
      obtain ⟨w,hw⟩ := hqW (Multiplicative.ofAdd v)
      have hwv : (qW w).toAdd = v := congrArg Multiplicative.toAdd hw
      have hwA : (w : G) ∈ A := by
        refine ⟨w.property,?_⟩
        intro y hy
        let x : X := ⟨y,hYX hy⟩
        apply (hp x w).mp
        rw [hwv]
        exact (Submodule.mem_dualCoannihilator v).mp hv (qX x).toAdd
          (show qX x ∈ (Y.subgroupOf X).map qX from mem_map_of_mem qX hy)
      have hwker : w ∈ qW.ker := hkerW.ge (hAz.le hwA)
      have hh : (qW w).toAdd = 0 := congrArg Multiplicative.toAdd hwker
      exact hwv.symm.trans hh
    have hP : P = ⊤ := by
      rw [←Subspace.dualCoannihilator_dualAnnihilator_eq (W := P),hPbot,
        Submodule.dualAnnihilator_bot]
    apply le_antisymm hYX
    intro x hx
    have hm : (qX ⟨x,hx⟩).toAdd ∈ P := hP.ge (Submodule.mem_top)
    obtain ⟨y,hy,he⟩ := (show qX ⟨x,hx⟩ ∈ (Y.subgroupOf X).map qX from hm)
    have hk : (⟨x,hx⟩ : X)*y⁻¹ ∈ qX.ker := by
      change qX ((⟨x,hx⟩ : X)*y⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hmem : x*(y : G)⁻¹ ∈ K := hkerX.le hk
    have hh := Y.mul_mem (hKY hmem) hy
    change (x*(y : G)⁻¹)*(y : G) ∈ Y at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
  · left
    apply le_antisymm ?_ hKY
    intro y hy
    let x : X := ⟨y,hYX hy⟩
    have hq : qX x = 1 := by
      apply Multiplicative.toAdd.injective
      apply LinearMap.ext
      intro v
      obtain ⟨w,hw⟩ := hqW (Multiplicative.ofAdd v)
      have hwv : (qW w).toAdd=v := congrArg Multiplicative.toAdd hw
      change (qX x).toAdd v = 0
      rw [←hwv]
      exact (hp x w).mpr ((hAW.ge w.property).2 y hy)
    exact hkerX.le hq

end Theory.GroupTheory
