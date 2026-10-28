module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterEight

/-!
# The complete marked outer central-closure image

The genuine order-eight theorem selects the full product core in the
original weight-four stabilizer chart. This retains the same original
automizer embedding, the prescribed K action, every U vector, and the
even coordinate relabeling. In particular the full original automizer
maps onto the full hexacode group.

Source: Aschbacher--Smith12.7.18 and its following generation paragraph,
printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Select the literal full two-core without changing any original actor
or the chosen module coordinates. -/
theorem original_tripleSix_central_closure_outer_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    let v := (tripleSixPointCoordinates D a z).toAdd
    W ≤ (T : Subgroup G) ∧
    ∃ f : Automizer U →* HexAutomorphisms, Function.Bijective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (inducedAutomizer U K).map f = hexSign.ker ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) ∧
      (let N := (inducedAutomizer U W).map f
       N ≤ Hexacode.fullVectorStabilizer v ∧
       ∃ e : Hexacode.fullVectorStabilizer v ≃* DuadProduct,
         ∃ r : alternatingGroup (Fin 6),
           (∀ g : Hexacode.fullVectorStabilizer v,
             duadProductHom (e g) = r.val * hexCoordinateSixHom g.val * r.val⁻¹) ∧
           (∀ g : Hexacode.fullVectorStabilizer v,
             hexSign g.val = 1 ↔ (e g).1 = signPermTwo (e g).2) ∧
           (N.subgroupOf (Hexacode.fullVectorStabilizer v)).map e.toMonoidHom =
             productCore) := by
  let W := conjugateSpanBy (tripleSixPoint D a z)
    (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
  obtain ⟨hWT, f, hf, hfk, hK, hchart, hfix, _, _, e, r, he, heven, hcases, _⟩ :=
    original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot
  let v := (tripleSixPointCoordinates D a z).toAdd
  let N := (inducedAutomizer U W).map f
  let B := N.subgroupOf (Hexacode.fullVectorStabilizer v)
  let β := B.map e.toMonoidHom
  let E : inducedAutomizer U W ≃* β :=
    ((inducedAutomizer U W).equivMapOfInjective f hf).trans
      ((subgroupOfEquivOfLe hfix).symm.trans (B.equivMapOfInjective e.toMonoidHom e.injective))
  have hcard : Nat.card β = 8 := (Nat.card_congr E.toEquiv).symm.trans
    (original_tripleSix_central_closure_outer_eight h structural D a z hz hzT hnot houter).1
  have houtercase : f.range = ⊤ ∧ (β = centralFactor ∨ β = productCore) := by
    rcases hcases with hklein | hout
    · change β = (⊥ : Subgroup Two).prod core at hklein
      have hc : Nat.card ((⊥ : Subgroup Two).prod core) = 4 := by
        rw [Nat.card_congr ((⊥ : Subgroup Two).prodEquiv core).toEquiv,
          Nat.card_prod, card_bot, one_mul, core_card]
      rw [hklein, hc] at hcard
      omega
    · exact hout
  have hprod : β = productCore := by
    rcases houtercase.2 with hcentral | hprod
    · rw [hcentral, centralFactor_card] at hcard
      omega
    · exact hprod
  exact ⟨hWT, f, ⟨hf, MonoidHom.range_eq_top.mp houtercase.1⟩,
    hfk, hK, hchart, hfix, e, r, he, heven, hprod⟩

end CFSG.Quasithin.Chapter12.Section07
