module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Marked
public import Theory.Representation.HigherFieldBorelFixedSpaces.Natural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Restricting the field in the line-offender alternatives

For either SL₂ or SL₃ over a larger binary field, a diagonal element of the
standard Borel has no eigenvalue one on the natural module. The same is true
on two identical copies. A marked, orbit-generating subspace cannot be fixed
by that Borel. Thus the source comparison of this Borel with the normalizer
of the actual Thompson image forces the field degree to be one.

The B.4 normalizer comparison is an explicit model hypothesis. These lemmas
prove the ensuing field restriction; they neither assert B.4/B.5 classification
nor identify the original I₀. Central quotient coordinates retain every
central extension, without requiring a split action on the original module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1154, using B.4.2 and B.5.1 (pp.86 and 99).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Representation.HigherFieldBorelFixedSpaces
open Matrix Matrix.SpecialLinearGroup Matrix.PSL3.LinearThree
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
  {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem large_card {n : ℕ} (hn : 1 < n) (hc : Nat.card F = 2 ^ n) :
    2 < Nat.card F := by
  rw [hc]
  have := Nat.pow_lt_pow_right (by decide : 1 < 2) hn
  simpa only [pow_one] using this

omit [CharP F 2] in
/-- The rank-one field remains unrestricted until the Borel comparison is used. -/
theorem linearTwo_field_degree_eq_one
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 2))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : rankOneBorel F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(2,F))) :
    n = 1 := by
  by_contra h
  exact d.model_fixedSpace_ne_bot c _ hB (sl2_borel_fixedSpace (large_card (by omega) hc))

/-- The natural rank-two case. In the source the degree is odd; the fixed-space
argument also works without that additional restriction. -/
theorem linearThree_field_degree_eq_one
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 3))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : borelSL F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(3,F))) :
    n = 1 := by
  by_contra h
  exact d.model_fixedSpace_ne_bot c _ hB (sl3_borel_fixedSpace (large_card (by omega) hc))

private theorem fixedSpace_prod_eq_bot {L X : Type*} [Group L]
    [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) L X) (B : Subgroup L)
    (h : fixedSpace σ B = ⊥) : fixedSpace (σ.prod σ) B = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have h₁ : v.1 ∈ fixedSpace σ B := fun b => congrArg Prod.fst (hv b)
  have h₂ : v.2 ∈ fixedSpace σ B := fun b => congrArg Prod.snd (hv b)
  apply Prod.ext
  · change v.1 = (0 : X)
    simpa only [h, Submodule.mem_bot] using h₁
  · change v.2 = (0 : X)
    simpa only [h, Submodule.mem_bot] using h₂

/-- The doubled natural rank-two case uses the same actor on both summands. -/
theorem doubleLinearThree_field_degree_eq_one
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ
      ((binaryNatural (F := F) 3).prod (binaryNatural (F := F) 3)))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : borelSL F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(3,F))) :
    n = 1 := by
  by_contra h
  exact d.model_fixedSpace_ne_bot c _ hB
    (fixedSpace_prod_eq_bot _ _ (sl3_borel_fixedSpace (large_card (by omega) hc)))

private noncomputable def fieldTwoEquiv (hc : Nat.card F = 2) : F ≃+* ZMod 2 := by
  let := Fintype.ofFinite F
  exact (ZMod.ringEquiv F (by simpa only [Nat.card_eq_fintype_card] using hc)).symm

/-- The rank-one result gives an actual S₃ group equivalence, while leaving
the original field/module coordinates available to the consumer. -/
theorem linearTwo_equiv_symmetricThree
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 2))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : rankOneBorel F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(2,F))) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) := by
  have hcard : Nat.card F = 2 := by rw [hc, linearTwo_field_degree_eq_one d c hn hc hB, pow_one]
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  exact ⟨c.actor.trans ((Atlas.fieldEquivSL 2 (fieldTwoEquiv hcard)).trans e)⟩

/-- The natural rank-two result identifies the actual actor with SL₃(2). -/
theorem linearThree_equiv_binary
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ (binaryNatural (F := F) 3))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : borelSL F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(3,F))) :
    Nonempty (D ≃* SL(3,ZMod 2)) := by
  have hcard : Nat.card F = 2 := by rw [hc, linearThree_field_degree_eq_one d c hn hc hB, pow_one]
  exact ⟨c.actor.trans (Atlas.fieldEquivSL 3 (fieldTwoEquiv hcard))⟩

/-- The doubled natural result retains the same SL₃(2) actor on both copies. -/
theorem doubleLinearThree_equiv_binary
    (d : MarkedNormalizer ρ J)
    (c : CentralQuotientCoordinates ρ
      ((binaryNatural (F := F) 3).prod (binaryNatural (F := F) 3)))
    {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ n)
    (hB : borelSL F ≤ Subgroup.normalizer (J.map c.actor.toMonoidHom : Set SL(3,F))) :
    Nonempty (D ≃* SL(3,ZMod 2)) := by
  have hcard : Nat.card F = 2 := by
    rw [hc, doubleLinearThree_field_degree_eq_one d c hn hc hB, pow_one]
  exact ⟨c.actor.trans (Atlas.fieldEquivSL 3 (fieldTwoEquiv hcard))⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
