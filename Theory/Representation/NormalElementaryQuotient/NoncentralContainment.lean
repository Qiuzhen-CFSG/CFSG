module
public import Theory.Representation.NormalElementaryQuotient.IrrPlusCommutator

/-!
# Noncentral subgroups contain an Irr⁺ moved module

An invariant subgroup of a normal elementary abelian group is an actual
binary subspace. If its perfect actor moves it, the Irr⁺ comparison gives
the full moved subspace. Translating through the original conjugation
quotient places the ambient subgroup commutator inside that subgroup.
No equality of the two action kernels is needed.

Source application: Aschbacher--Smith,12.6.11, printed p.825.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace Representation.NormalElementaryQuotient
variable {G H : Type*} [Group G] [Group H]

/-- A noncentral invariant subgroup contains the entire Irr⁺ moved space. -/
theorem commutator_le_of_noncentral_invariant
    (U W B : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hWU : W ≤ U) (hn : B ≤ normalizer (W : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    [Group.IsPerfect (B.map q)]
    (hi : IsIrrPlus (representation U q hq hker) (B.map q)
      (subspaceCommutator (representation U q hq hker) ⊤ (B.map q)))
    (hm : ⁅W,B⁆ ≠ ⊥) : ⁅U,B⁆ ≤ W := by
  let ρ := representation U q hq hker
  let S : Submodule (ZMod 2) (Additive U) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf U).toAddSubgroup
  have hs : B.map q ≤ subspaceStabilizer ρ S := by
    apply le_subspaceStabilizer
    rintro _ ⟨b,hb,rfl⟩ u hu
    change ((ρ (q b) u).toMul : G) ∈ W
    rw [representation_apply]
    exact (mem_normalizer_iff.mp (hn hb) u.toMul.val).mp hu
  have hnon : ¬ S ≤ fixedSpace ρ (B.map q) := by
    intro hf
    apply hm
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro b hb w hw
    let u : Additive U := Additive.ofMul ⟨w,hWU hw⟩
    have he := congrArg (fun z : Additive U => (z.toMul : G))
      (hf (show u ∈ S from hw) ⟨q b,mem_map_of_mem q hb⟩)
    change ((ρ (q b) u).toMul : G) = w at he
    rw [representation_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have he := moved_eq_of_noncentral_invariant ρ (B.map q) hi S hs hnon
  have hmov : subspaceCommutator ρ ⊤ (B.map q) ≤ S := by
    rw [←he]
    apply Submodule.span_le.mpr
    rintro _ ⟨b,hb,u,hu,rfl⟩
    exact S.sub_mem ((hs hb u).mpr hu) hu
  intro x hx
  let u : Additive U := Additive.ofMul ⟨x,commutator_le_left U B hx⟩
  apply hmov (show u ∈ subspaceCommutator ρ ⊤ (B.map q) from ?_)
  rw [←commutatorSpace_eq U q hq hker B]
  exact hx
end Representation.NormalElementaryQuotient
