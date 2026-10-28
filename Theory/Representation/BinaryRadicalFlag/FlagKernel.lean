module
public import Theory.LinearAlgebra.BinaryTriangularPGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# The kernel of a finite linear flag

The full setwise flag stabilizer normalizes the subgroup acting trivially
on successive layers. Every such element has nilpotent displacement:
each application lowers the flag by one step. A faithful binary action
therefore makes this kernel a two-group, with no triangular-basis choice.

Source: Aschbacher (1981), A pushing up theorem for finite groups, 8.2(7),
pp.73–74; Aschbacher–Smith C.2.7(3), printed pp.145–146.
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryRadical
open Subgroup
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)

def stabilizer (W : Submodule F V) : Subgroup G where
  carrier := {g | ∀ v, ρ g v ∈ W ↔ v ∈ W}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul,Module.End.mul_apply] using (hg (ρ h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
      using (hg (ρ g⁻¹ v)).symm

def flagStabilizer {k : ℕ} (W : Fin (k+1) → Submodule F V) : Subgroup G :=
  ⨅ i, stabilizer ρ (W i)

theorem mem_flagStabilizer {k : ℕ} (W : Fin (k+1) → Submodule F V) {g : G} :
    g ∈ flagStabilizer ρ W ↔ ∀ i v, ρ g v ∈ W i ↔ v ∈ W i := by
  simp only [flagStabilizer,Subgroup.mem_iInf]
  rfl

def flagKernel {k : ℕ} (W : Fin (k+1) → Submodule F V) : Subgroup G where
  carrier := {g | g ∈ flagStabilizer ρ W ∧
    ∀ (i : Fin k) v, v ∈ W i.succ → ρ g v - v ∈ W i.castSucc}
  one_mem' := by
    refine ⟨one_mem _,?_⟩
    intro i v hv
    simp
  mul_mem' := by
    rintro g h ⟨hg,hgd⟩ ⟨hh,hhd⟩
    refine ⟨mul_mem hg hh,?_⟩
    intro i v hv
    have hm := ((mem_flagStabilizer ρ W).mp hh i.succ v).mpr hv
    simpa only [map_mul,Module.End.mul_apply,sub_add_sub_cancel] using
      (W i.castSucc).add_mem (hgd i (ρ h v) hm) (hhd i v hv)
  inv_mem' := by
    rintro g ⟨hg,hgd⟩
    refine ⟨inv_mem hg,?_⟩
    intro i v hv
    have hm := ((mem_flagStabilizer ρ W).mp ((flagStabilizer ρ W).inv_mem hg) i.succ v).mpr hv
    simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
      Module.End.one_apply,neg_sub] using (W i.castSucc).neg_mem (hgd i (ρ g⁻¹ v) hm)

theorem flagStabilizer_le_normalizer {k : ℕ} (W : Fin (k+1) → Submodule F V) :
    flagStabilizer ρ W ≤ normalizer (flagKernel ρ W : Set G) := by
  rw [le_set_normalizer_iff]
  intro g hg t ht
  refine ⟨(flagStabilizer ρ W).mul_mem ((flagStabilizer ρ W).mul_mem hg ht.1)
    ((flagStabilizer ρ W).inv_mem hg),?_⟩
  intro i v hv
  have hi := ((mem_flagStabilizer ρ W).mp ((flagStabilizer ρ W).inv_mem hg) i.succ v).mpr hv
  have hd := ht.2 i (ρ g⁻¹ v) hi
  have hm := ((mem_flagStabilizer ρ W).mp hg i.castSucc _).mpr hd
  simpa only [map_sub,←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
    Module.End.one_apply,mul_assoc] using hm

theorem flagKernel_isPGroup [Nontrivial V] [CharP F 2]
    (hρ : Function.Injective ρ) {k : ℕ} (W : Fin (k+1) → Submodule F V)
    (hzero : W 0 = ⊥) (hlast : W (Fin.last k) = ⊤) :
    IsPGroup 2 (flagKernel ρ W) := by
  let : ExpChar (Module.End F V) 2 := expChar_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective F (Module.End F V)) 2
  apply IsPGroup.of_injective_unipotent_binary (ρ.comp (flagKernel ρ W).subtype)
    (hρ.comp Subtype.val_injective)
  intro g
  have hp : ∀ (i : ℕ) (hi : i ≤ k) (v : V),
      v ∈ W ⟨i,Nat.lt_succ_of_le hi⟩ → ((ρ g - 1)^i) v = 0 := by
    intro i
    induction i with
    | zero =>
      intro hi v hv
      rw [show (⟨0,Nat.lt_succ_of_le hi⟩ : Fin (k+1)) = 0 from rfl,hzero] at hv
      simpa only [pow_zero,Module.End.one_apply,Submodule.mem_bot] using hv
    | succ i ih =>
      intro hi v hv
      have hi' : i < k := by omega
      have hd := g.property.2 ⟨i,hi'⟩ v hv
      have hh := ih (Nat.le_of_lt hi') (ρ g v - v) hd
      simpa only [pow_succ,Module.End.mul_apply,LinearMap.sub_apply,Module.End.one_apply] using hh
  refine ⟨k,?_⟩
  apply LinearMap.ext
  intro v
  exact hp k le_rfl v (hlast.symm ▸ Submodule.mem_top)

end Representation.BinaryRadical
