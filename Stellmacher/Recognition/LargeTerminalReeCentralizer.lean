module

public import Stellmacher.Recognition.LargeTerminalInvolutionCentralizerQuotient
public import Stellmacher.Recognition.LargeTerminalFiveFixedFour
public import Stellmacher.Recognition.LargeTerminalFiveFixedCyclic
public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalReeRootRelations
public import Theory.SpecificGroups.ReeTwo.Recognition
public import Theory.GroupTheory.SelfCentralizingCore
public import Theory.GroupAction.IndexTwoFiveFixedPoints

/-!
# Root recognition for the upper terminal involution centralizer

The order-4096 endpoint supplies an omega-central involution whose full
centralizer equals the second local group, with its actual two-core of
order 1024. The older centralizer and fixed-point inputs remain exported.

The cyclic five-fixed subgroup and the actual root extraction supply ten core
roots, root 1 and a Weyl element satisfying Shinoda's relations. The verified
model's universal map is injective because its last root survives. Equality
of group orders then gives an isomorphism, preserving each chosen generator
and carrying the model core onto the actual two-core.

`ree_centralizer_equiv_of_large_card` completes this identification from the
original terminal context at any designated omega-central involution.
`exists_ree_centralizer_of_large_card` also supplies that involution and the
Sylow containment and trivial odd core needed by the recognition consumer.

Source: Shinoda, Odd order extensions of the Ree groups (1975), pp.81–83,
and Thompson VI, pp.629–630.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

/-- Recognition inputs retaining the actual Sylow and full centralizer. -/
public theorem LargeTerminalContext.ree_centralizer_inputs_of_large_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 4096) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      (S0 : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = twoCoreIn ctx.second ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 1024 ∧
      Group.IsSolvable (centralizer ({z} : Set G)) ∧
      IsCharacteristicTwoType (centralizer ({z} : Set G)) ∧
      pPrimeCore 2 (centralizer ({z} : Set G)) = ⊥ := by
  obtain ⟨z, hz, hgen, hcore, hcard⟩ :=
    ctx.involution_centralizer_core_eq_of_large_card hS
  obtain ⟨hsolv, hchar⟩ := ctx.localStructure _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)
  refine ⟨z, hz, hgen, ?_, hcore, hcard, hsolv, hchar, ?_⟩
  · rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
    exact le_centralizer_iff.mpr ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))
  · let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hchar

/-- Identification from actual root relations, preserving every generator and
the full two-core. -/
public theorem LargeTerminalContext.ree_centralizer_equiv_of_root_relations
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (x : ReeTwo.CoreRoot → centralizer ({z} : Set G))
    (s w : centralizer ({z} : Set G))
    (hx : ReeTwo.CoreRelations x) (hs : ReeTwo.RootOneRelations s x)
    (hw : ∀ i, w * x i * w⁻¹ = x (ReeTwo.weylRoot i))
    (hc : ((s⁻¹) ^ 2 * w) ^ 5 = 1) (ha : (s⁻¹) ^ 4 = 1)
    (h : s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2)
    (hxQ : ∀ i, x i ∈ pCore 2 (centralizer ({z} : Set G)))
    (hxz : (x 9 : G) = z) :
    ∃ e : ReeTwo.Centralizer ≃* centralizer ({z} : Set G),
      (∀ i, e (ReeTwo.Centralizer.root i) = x i) ∧
      e ReeTwo.Centralizer.rootOne = s ∧ e ReeTwo.Centralizer.weyl = w ∧
      ReeTwo.Centralizer.core.map e.toMonoidHom =
        pCore 2 (centralizer ({z} : Set G)) := by
  have hcard : Nat.card (centralizer ({z} : Set G)) = 20480 := by
    rw [ctx.involution_centralizer_eq_second hS z hz hgen]
    exact ctx.second_card_of_large_card hS
  have hxne : x 9 ≠ 1 := by
    intro he
    have hz1 : z = 1 := hxz.symm.trans (congrArg Subtype.val he)
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  let e := MulEquiv.ofBijective (ReeTwo.Centralizer.lift hx hs hw hc ha h)
    (ReeTwo.Centralizer.lift_bijective hcard hx hs hw hc ha h hxne)
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ReeTwo.Centralizer.lift_root hx hs hw hc ha h i
  · exact ReeTwo.Centralizer.lift_rootOne hx hs hw hc ha h
  · exact ReeTwo.Centralizer.lift_weyl hx hs hw hc ha h
  · apply eq_of_le_of_card_ge (ReeTwo.Centralizer.lift_core_le hx hs hw hc ha h _ hxQ)
    rw [card_map_of_injective e.injective, ReeTwo.Centralizer.core_card,
      (ctx.involution_centralizer_core_eq_at_generator hS z hgen).2]

/-- The full centralizer at a designated omega-central involution is the
verified Ree centralizer. The isomorphism marks root 12 by that involution
and carries the model core onto the actual full-centralizer two-core. -/
public theorem LargeTerminalContext.ree_centralizer_equiv_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ e : ReeTwo.Centralizer ≃* centralizer ({z} : Set G),
      (e (ReeTwo.Centralizer.root 9) : G) = z ∧
      ReeTwo.Centralizer.core.map e.toMonoidHom =
        pCore 2 (centralizer ({z} : Set G)) := by
  obtain ⟨A, hA, hAP, hAN, hcard, hfixed, hcyc⟩ :=
    ctx.exists_five_fixed_cyclic_of_large_card hS
  obtain ⟨x, s, w, hx, hs, hw, hc, ha, h, hxQ, hxz⟩ :=
    ctx.exists_ree_root_relations_of_cyclic hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  obtain ⟨e, he, _, _, hcore⟩ := ctx.ree_centralizer_equiv_of_root_relations
    hS z hz hgen x s w hx hs hw hc ha h hxQ hxz
  exact ⟨e, (congrArg Subtype.val (he 9)).trans hxz, hcore⟩

/-- The original terminal hypotheses supply the full Ree centralizer packet,
including a central involution of the prescribed Sylow, trivial odd core,
and an isomorphism retaining the actual two-core and central root. -/
public theorem LargeTerminalContext.exists_ree_centralizer_of_large_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S : Subgroup G) ∧
      (S : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      pPrimeCore 2 (centralizer ({z} : Set G)) = ⊥ ∧
      ∃ e : ReeTwo.Centralizer ≃* centralizer ({z} : Set G),
        (e (ReeTwo.Centralizer.root 9) : G) = z ∧
        ReeTwo.Centralizer.core.map e.toMonoidHom =
          pCore 2 (centralizer ({z} : Set G)) := by
  obtain ⟨z, hz, hgen, hSC, _, _, _, _, hodd⟩ :=
    ctx.ree_centralizer_inputs_of_large_card hS
  exact ⟨z, hz, hgen, hSC, hodd,
    ctx.ree_centralizer_equiv_of_large_card hS z hz hgen⟩

end Stellmacher.Recognition
