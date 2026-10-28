module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair
public import Theory.AtlasPort.LinearGroups.G2.BinarySign
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Identifying the binary derived group

A commutator in the root core is the long root A(1). Conjugacy and normal
closure put the long-root subgroup inside the derived group; the hexagon
sign character gives the reverse inclusion. Thus the index-two model used
for the restriction is the actual commutator subgroup of G₂(2).
Source: the binary exception calculation in the licensed ATLAS port, and
Aschbacher–Smith, Lemma 14.2.21, printed p.988.
-/

@[expose] public section

namespace Atlas.G2.BinaryParabolicPair
open Atlas.G2.Explicit BinaryCore
open scoped commutatorElement
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem rootA_one_mem_commutator : rootA (1 : ZMod 2) ∈ commutator (Model (ZMod 2)) := by
  have he : ⁅(⟨0,1,0,0,0⟩ : Coordinates), (⟨0,0,0,0,1⟩ : Coordinates)⁆ = involution := by
    decide +kernel
  rw [← embedding_involution, ← he, map_commutatorElement]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The index-two long-root normal closure is the actual derived subgroup. -/
theorem commutator_eq_longRootClosure :
    commutator (Model (ZMod 2)) = BinaryException.H := by
  apply le_antisymm
  · rw [← BinaryException.lineSign_kernel]
    exact Abelianization.commutator_subset_ker Binary.lineSign
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨⟨a,b⟩,rfl⟩
    change rootA a * rootB b ∈ commutator (Model (ZMod 2))
    have hA (a : ZMod 2) : rootA a ∈ commutator (Model (ZMod 2)) := by
      have hb : ∀ a : ZMod 2, a=0 ∨ a=1 := by decide +kernel
      rcases hb a with rfl | rfl
      · rw [rootA_zero]; exact Subgroup.one_mem _
      · exact rootA_one_mem_commutator
    apply Subgroup.mul_mem _ (hA a)
    rw [← weylR_rootA]
    exact (inferInstance : (commutator (Model (ZMod 2))).Normal).conj_mem _ (hA b) _

theorem quotientBit_ne_one : BinaryException.quotientBit ≠ 1 := by
  intro h
  have hm : rootF (1 : ZMod 2) ∈ BinaryException.H :=
    (QuotientGroup.eq_one_iff _).mp h
  rw [← BinaryException.lineSign_kernel] at hm
  have he := MonoidHom.mem_ker.mp hm
  rw [Binary.lineSign_rootF_one] at he
  exact (by decide : (-1 : ℤˣ) ≠ 1) he


end Atlas.G2.BinaryParabolicPair
