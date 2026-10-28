module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# A cyclic normal subgroup controlling odd subgroups

The condition below supplies a cyclic normal subgroup whose quotient has
cyclic p-subgroups for each odd prime p. It is inherited by injective group
homomorphisms: pull back the normal subgroup and embed the resulting quotient.
This is the structural input for the outer-automorphism inspection in
Aschbacher–Smith, combined 1 March 2004 manuscript, printed p.510.
-/

@[expose] public section
namespace Theory.GroupTheory
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A cyclic normal subgroup with cyclic odd-prime subgroups in its quotient. -/
def HasCyclicNormalOddQuotient (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, ∃ _ : N.Normal, IsCyclic N ∧
    ∀ p : ℕ, p.Prime → Odd p → ∀ U : Subgroup (G ⧸ N),
      IsPGroup p U → IsCyclic U

/-- The structural condition passes to every injectively embedded group. -/
theorem HasCyclicNormalOddQuotient.of_injective
    (h : HasCyclicNormalOddQuotient G) (f : H →* G) (hf : Function.Injective f) :
    HasCyclicNormalOddQuotient H := by
  obtain ⟨N, hN, hc, hq⟩ := h
  let := hN
  let := hc
  let K := N.comap f
  let i : K →* N := (f.comp K.subtype).codRestrict N (fun x => x.property)
  have hi : Function.Injective i := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  have hK : IsCyclic K := isCyclic_of_injective i hi
  let q : H ⧸ K →* G ⧸ N := QuotientGroup.map K N f le_rfl
  have hqi : Function.Injective q := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact (QuotientGroup.ker_map K N f le_rfl).trans
      (QuotientGroup.map_mk'_self K)
  refine ⟨K, inferInstance, hK, ?_⟩
  intro p hp ho U hU
  let := hq p hp ho (U.map q) (hU.map q)
  exact isCyclic_of_injective (U.equivMapOfInjective q hqi).toMonoidHom
    (U.equivMapOfInjective q hqi).injective

/-- If all odd-prime subgroups are already cyclic, the trivial kernel suffices. -/
theorem hasCyclicNormalOddQuotient_of_odd_subgroups_cyclic
    (h : ∀ p : ℕ, p.Prime → Odd p → ∀ U : Subgroup G,
      IsPGroup p U → IsCyclic U) : HasCyclicNormalOddQuotient G := by
  refine ⟨⊥, inferInstance, inferInstance, ?_⟩
  intro p hp ho U hU
  let e : G ⧸ (⊥ : Subgroup G) ≃* G := QuotientGroup.quotientBot
  let := h p hp ho (U.map e.toMonoidHom) (hU.map e.toMonoidHom)
  exact isCyclic_of_injective (U.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom
    (U.equivMapOfInjective e.toMonoidHom e.injective).injective

/-- Cyclic groups satisfy the condition with trivial kernel. -/
theorem hasCyclicNormalOddQuotient_of_isCyclic [IsCyclic G] :
    HasCyclicNormalOddQuotient G :=
  hasCyclicNormalOddQuotient_of_odd_subgroups_cyclic (fun _ _ _ _ _ => inferInstance)

/-- Two-groups have no nontrivial odd-prime subgroups. -/
theorem hasCyclicNormalOddQuotient_of_isPGroup_two (hG : IsPGroup 2 G) :
    HasCyclicNormalOddQuotient G := by
  apply hasCyclicNormalOddQuotient_of_odd_subgroups_cyclic
  intro p _ ho U hU
  have hc : Nat.Coprime p 2 := ho.coprime_two_right
  have hd : Disjoint U U := hU.disjoint_of_coprime (hG.to_subgroup U) hc
  have hbot : U = ⊥ := disjoint_self.mp hd
  rw [hbot]
  infer_instance

end Theory.GroupTheory
