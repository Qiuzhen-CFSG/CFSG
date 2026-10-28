module

public import Theory.GroupTheory.SelfCentralizingNormalFourRecognition
public import Theory.GroupTheory.QuotientKernelComplement
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# A complement to a self-centralizing normal four-group

In a group of order twenty-four a self-centralizing normal two-subgroup of
order four admits a complement. Recognition identifies the group with S₄;
the given normal subgroup is its two-core, and a point stabilizer complements
that core. The complement is pulled back along the actual equivalence.

This supplies the splitting step for the diagonal quotient of a conjugation
fiber product, including the second Tits parabolic reconstruction.
-/

public section
open Subgroup

public theorem exists_complement_of_selfCentralizing_normal_four
    {G : Type*} [Group G] [Finite G] (U : Subgroup G) [U.Normal]
    (hU : IsPGroup 2 U) (hcard : Nat.card U = 4)
    (hc : centralizer (U : Set G) ≤ U) (hG : Nat.card G = 24) :
    ∃ L : Subgroup G, U.IsComplement' L := by
  classical
  obtain ⟨e⟩ := mulEquiv_perm_four_of_selfCentralizing_normal_four U hU hcard hc hG
  let K := MulAction.stabilizer (Equiv.Perm (Fin 4)) (0 : Fin 4)
  have hK : Nat.card K = 6 := by
    change Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 4)) (0 : Fin 4)) = 6
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have heU : U.map e.toMonoidHom =
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core := by
    have hn : (U.map e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    let := hn
    apply eq_of_le_of_card_ge
    · rw [Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq]
      exact le_sSup ⟨hn,hU.map e.toMonoidHom⟩
    · rw [Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card,
        ← Nat.card_congr (U.equivMapOfInjective e.toMonoidHom e.injective).toEquiv,hcard]
  have hd : Disjoint (U.map e.toMonoidHom) K := by
    rw [heU,Subgroup.disjoint_def]
    intro g
    exact (show ∀ g : Equiv.Perm (Fin 4),
      g ∈ Theory.SpecificGroups.SymmetricSix.DuadCalculation.core → g 0 = 0 → g = 1
      by decide +kernel) g
  have hcomp : (U.map e.toMonoidHom).IsComplement' K := by
    apply isComplement'_of_card_mul_and_disjoint _ hd
    rw [heU,Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card,hK,
      Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  refine ⟨K.comap e.toMonoidHom,
    QuotientKernelComplement.complement_comap e.toMonoidHom U K ?_ hcomp⟩
  rw [e.toMonoidHom.ker_eq_bot e.injective]
  exact disjoint_bot_right
