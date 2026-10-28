module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-!
# A binary seed moved by an inverted cubic

A fixed-point-free cubic has zero norm. Its translates therefore put a
seed in its own commutator space. If the seed is fixed by an inverter,
it intersects its cubic translate trivially. Their sum is the whole
commutator space, whose dimension is twice the seed dimension.

This calculation applies to the literal central residual and Sylow fixed
plane in `MarkedCubicRecognition.CentralSeed`; it does not require a
classification or an irreducible decomposition of the ambient module.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.InvertedCubicSeed
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- An inverted fixed-point-free cubic doubles every subspace fixed by the inverter. -/
theorem moved_seed_and_finrank [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (c s : G) (hc : orderOf c = 3)
    (hi : s * c = c ^ 2 * s) (hf : ∀ v, ρ c v = v → v = 0)
    (Z : Submodule (ZMod 2) V) (hZ : ∀ v ∈ Z, ρ s v = v) :
    Z ≤ subspaceCommutator ρ Z (zpowers c) ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ Z (zpowers c)) =
        2 * Module.finrank (ZMod 2) Z := by
  classical
  have hc3 (v : V) : ρ c (ρ c (ρ c v)) = v := by
    change (ρ c * (ρ c * ρ c)) v = v
    rw [←map_mul,←map_mul]
    rw [show c * (c*c) = c^3 by simp [pow_succ,mul_assoc],←hc,pow_orderOf_eq_one,map_one]
    rfl
  have hnorm (v : V) : v + ρ c v + ρ c (ρ c v) = 0 := by
    apply hf
    rw [map_add,map_add,hc3]
    abel
  have htwice (v : V) : v + v = 0 := by
    have hh := two_smul (ZMod 2) v
    rw [show (2 : ZMod 2) = 0 by decide,zero_smul] at hh
    exact hh.symm
  have hneg (v : V) : -v = v := neg_eq_iff_add_eq_zero.mpr (htwice v)
  have hquad (v : V) : ρ c (ρ c v) = v + ρ c v := by
    have h := eq_neg_of_add_eq_zero_right (hnorm v)
    simpa only [neg_add,hneg] using h
  have hsi (v : V) : ρ s (ρ c v) = ρ c (ρ c (ρ s v)) := by
    change (ρ s * ρ c) v = (ρ c * (ρ c * ρ s)) v
    rw [←map_mul,←map_mul,←map_mul,hi,pow_two,mul_assoc]
  let U := Z ⊔ Z.map (ρ c)
  have hdis : Disjoint Z (Z.map (ρ c)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hv'
    obtain ⟨w,hw,rfl⟩ := hv'
    have he : ρ c (ρ c w) = ρ c w := by
      have hh := hsi w
      rw [hZ w hw,hZ (ρ c w) hv] at hh
      exact hh.symm
    exact hf _ he
  have heq : subspaceCommutator ρ Z (zpowers c) = U := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,v,hv,rfl⟩
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp ha)
      have hil : i < 3 := by simpa only [hc,Finset.mem_range] using hi
      have hvU : v ∈ U := (show Z ≤ U from le_sup_left) hv
      have hcvU : ρ c v ∈ U := (show Z.map (ρ c) ≤ U from le_sup_right) ⟨v,hv,rfl⟩
      interval_cases i
      · simp
      · simpa using U.sub_mem hcvU hvU
      · have hh := U.sub_mem (U.add_mem hvU hcvU) hvU
        change ρ (c^2) v-v ∈ U
        rw [pow_two,map_mul,Module.End.mul_apply,hquad]
        exact hh
    · have hZle : Z ≤ subspaceCommutator ρ Z (zpowers c) := by
        intro v hv
        have h1 : ρ c v - v ∈ subspaceCommutator ρ Z (zpowers c) :=
          Submodule.subset_span ⟨c,mem_zpowers c,v,hv,rfl⟩
        have h2 : ρ c (ρ c v) - v ∈ subspaceCommutator ρ Z (zpowers c) := by
          have hh : ρ (c^2) v - v ∈ subspaceCommutator ρ Z (zpowers c) :=
            Submodule.subset_span ⟨c^2,(zpowers c).pow_mem (mem_zpowers c) 2,v,hv,rfl⟩
          simpa only [pow_two,map_mul,Module.End.mul_apply] using hh
        have hh := (subspaceCommutator ρ Z (zpowers c)).add_mem h1 h2
        have he : (ρ c v-v)+(ρ c (ρ c v)-v)=v := by
          rw [hquad,sub_eq_add_neg,sub_eq_add_neg,hneg]
          have hv2 := htwice v
          have hc2 := htwice (ρ c v)
          calc
            _ = v + (v+v) + (ρ c v+ρ c v) := by abel
            _ = v := by rw [hv2,hc2,add_zero,add_zero]
        exact he ▸ hh
      refine sup_le hZle ?_
      rintro v ⟨w,hw,rfl⟩
      have hh := (subspaceCommutator ρ Z (zpowers c)).add_mem
        (Submodule.subset_span ⟨c,mem_zpowers c,w,hw,rfl⟩) (hZle hw)
      simpa only [sub_add_cancel] using hh
  have hdim : Module.finrank (ZMod 2) (Z.map (ρ c)) = Module.finrank (ZMod 2) Z := by
    exact (LinearEquiv.ofLinearMap (ρ c) (ρ c⁻¹) (by
      ext v
      change ρ c (ρ c⁻¹ v) = v
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
      rfl) (by
      ext v
      change ρ c⁻¹ (ρ c v) = v
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one]
      rfl)).finrank_map_eq Z
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq Z (Z.map (ρ c))
  rw [hdis.eq_bot,finrank_bot,add_zero,hdim] at hadd
  refine ⟨?_,?_⟩
  · rw [heq]
    exact le_sup_left
  rw [heq]
  change Module.finrank (ZMod 2) (Z ⊔ Z.map (ρ c) : Submodule (ZMod 2) V) = _
  omega
end Representation.InvertedCubicSeed
