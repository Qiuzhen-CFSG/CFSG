module
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Mathlib.GroupTheory.GroupAction.Basic
public import Theory.Representation.BinaryOffender.IrreducibleOrbitAction
/-!
# Recovering a component of a permuted Sylow-fixed seed

The sum of the orbit of a support-stabilizer-fixed vector is globally
Sylow-fixed and differs from the original vector only in the other supports.
Coprime averaging on an odd fully moved actor then recovers that original
component inside any invariant subspace containing the orbit sum.

This is the component-seed step of Aschbacher--Smith 15.1.2, printed p.1085.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V ι : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Finite ι]
  (ρ : Representation (ZMod 2) G V)
omit [Finite G] [Finite ι] in
theorem fixed_orbit_trace (S : Subgroup G) (π : G →* Equiv.Perm ι)
    (U : ι → Submodule (ZMod 2) V) (X : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → U j ≤ fixedSpace ρ (X i))
    (hs : ∀ g i, (U i).map (ρ g) = U (π g i))
    (i : ι) (v : V) (hv : v ∈ U i)
    (hfix : v ∈ fixedSpace ρ (S ⊓ subspaceStabilizer ρ (U i))) :
    ∃ z : V, z ∈ fixedSpace ρ S ∧
      z ∈ ⨆ s : S, U (π s i) ∧ z - v ∈ fixedSpace ρ (X i) := by
  classical
  let : MulAction S V := {
    smul s v := ρ s v
    one_smul v := by change ρ (1:G) v = v; simp
    mul_smul s t v := by
      change ρ ((s:G)*(t:G)) v = ρ s (ρ t v)
      rw [map_mul,Module.End.mul_apply] }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let O := MulAction.orbit S v
  let := Fintype.ofFinite O
  let z : V := ∑ w : O, (w:V)
  have hz (s : S) : ρ s z = z := by
    let e : O ≃ O := {
      toFun w := ⟨s • (w:V), (by
        obtain ⟨t,ht⟩ := w.property
        exact ⟨s*t,by change (s*t) • v = s • (w:V); rw [mul_smul]; exact congrArg (fun x : V => s • x) ht⟩)⟩
      invFun w := ⟨s⁻¹ • (w:V), (by
        obtain ⟨t,ht⟩ := w.property
        exact ⟨s⁻¹*t,by change (s⁻¹*t) • v = s⁻¹ • (w:V); rw [mul_smul]; exact congrArg (fun x : V => s⁻¹ • x) ht⟩)⟩
      left_inv w := Subtype.ext (inv_smul_smul s (w:V))
      right_inv w := Subtype.ext (smul_inv_smul s (w:V)) }
    change ρ s (∑ w : O, (w:V)) = ∑ w : O, (w:V)
    rw [map_sum]
    exact e.sum_comp (fun w : O => (w:V))
  have hwo (w : O) : ∃ s : S, ρ s v = (w:V) := w.property
  have hother (w : O) (hw : (w:V) ≠ v) : (w:V) ∈ fixedSpace ρ (X i) := by
    obtain ⟨s,heq⟩ := hwo w
    rw [←heq]
    have hne : i ≠ π s i := by
      intro he
      have hstab : (s:G) ∈ subspaceStabilizer ρ (U i) := by
        apply (subspace_map_eq_iff ρ (U i) s).mp
        rw [hs,←he]
      exact hw (heq.symm.trans (hfix ⟨s,⟨s.property,hstab⟩⟩))
    exact hc i (π s i) hne (hs s i ▸ Submodule.mem_map_of_mem (f := ρ s) hv)
  refine ⟨z,hz,?_,?_⟩
  · apply Submodule.sum_mem
    intro w _
    obtain ⟨s,heq⟩ := hwo w
    rw [←heq]
    exact le_iSup (fun s : S => U (π s i)) s (hs s i ▸ Submodule.mem_map_of_mem (f := ρ s) hv)
  · let wv : O := ⟨v,MulAction.mem_orbit_self v⟩
    have hh : z = v + ∑ w ∈ Finset.univ.erase wv, (w:V) := by
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ wv)).symm
    rw [hh,add_sub_cancel_left]
    apply Submodule.sum_mem
    intro w hw
    exact hother w (fun he => (Finset.mem_erase.mp hw).1 (Subtype.ext he))
end Representation.BinaryOffender

open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
theorem odd_moved_component_mem (N : Subgroup G) [Finite N] (ho : Odd (Nat.card N))
    (R : Submodule (ZMod 2) V) (hR : N ≤ subspaceStabilizer ρ R)
    {z v : V} (hz : z ∈ R) (hv : v ∈ subspaceCommutator ρ ⊤ N)
    (hfix : z-v ∈ fixedSpace ρ N) : v ∈ R := by
  classical
  let := Fintype.ofFinite N
  have hcard : (Fintype.card N : ZMod 2) = 1 := by
    obtain ⟨k,hk⟩ := ho
    rw [←Nat.card_eq_fintype_card,hk]
    simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,Nat.cast_one,zero_add]
  let av : V →ₗ[ZMod 2] V := ∑ n : N, ρ n
  have hav (w : V) : av w = ∑ n : N, ρ n w := LinearMap.sum_apply _ _ _
  have hright (n : N) (w : V) : av (ρ n w) = av w := by
    simp only [hav,←Module.End.mul_apply,←map_mul]
    change (∑ m : N, ρ ((m*n:N):G) w) = ∑ m : N, ρ m w
    exact (Group.mulRight_bijective n).sum_comp (fun m : N => ρ m w)
  have hkill : subspaceCommutator ρ ⊤ N ≤ av.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,hn,w,_,rfl⟩
    change av (ρ n w-w) = 0
    rw [map_sub,hright ⟨n,hn⟩,sub_self]
  have hf : av (z-v) = z-v := by
    rw [hav]
    simp only [show ∀ n : N, ρ n (z-v) = z-v from hfix,
      Finset.sum_const,Finset.card_univ]
    rw [←Nat.cast_smul_eq_nsmul (ZMod 2),hcard,one_smul]
  have haz : av z = z-v := by
    simpa only [map_sub,show av v = 0 from hkill hv,sub_zero] using hf
  have haR : av z ∈ R := by
    rw [hav]
    exact R.sum_mem fun n _ => (hR n.property z).2 hz
  have hh := R.sub_mem hz (haz ▸ haR)
  simpa only [sub_sub_cancel] using hh
end Representation.BinaryOffender

namespace Representation.BinaryOffender
open Subgroup Representation
variable {G V ι : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- A fixed vector in one support is recovered from the global fixed seed,
using the odd actor which moves that support fully. -/
theorem fixed_support_seed_le (S : Subgroup G) (π : G →* Equiv.Perm ι)
    (U : ι → Submodule (ZMod 2) V) (X : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → U j ≤ fixedSpace ρ (X i))
    (hs : ∀ g i, (U i).map (ρ g) = U (π g i)) (i : ι)
    (N : Subgroup G) [Finite N] (ho : Odd (Nat.card N)) (hNX : N ≤ X i)
    (hm : U i ≤ subspaceCommutator ρ ⊤ N)
    (R : Submodule (ZMod 2) V) (hR : N ≤ subspaceStabilizer ρ R)
    (hseed : fixedSpace ρ S ⊓ (⨆ s : S, U (π s i)) ≤ R) :
    fixedSpace ρ (S ⊓ subspaceStabilizer ρ (U i)) ⊓ U i ≤ R := by
  intro v hv
  obtain ⟨z,hz,hzo,hfix⟩ := fixed_orbit_trace ρ S π U X hc hs i v hv.2 hv.1
  exact odd_moved_component_mem ρ N ho R hR (hseed ⟨hz,hzo⟩) (hm hv.2)
    (fun n => hfix ⟨n,hNX n.property⟩)
end Representation.BinaryOffender
