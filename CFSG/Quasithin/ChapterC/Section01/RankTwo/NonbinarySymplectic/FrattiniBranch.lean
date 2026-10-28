module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.InitialReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreRecognition
public import Theory.Quasithin.CoprimeRank

/-!
# The remaining premises in the field-four Frattini-small branch

The intrinsic MS input supplies normality, simplicity, faithfulness and SQTK
for the actual quotient component. Its order is computed from the supplied
symplectic equivalence. Thus the existing whole-core recognition theorem
requires only the field-four restriction and the Frattini commutator bound.
Both remain explicit here: this conditional branch does not prove C.1.32.

Source: MS93 (3.6)--(3.7), printed pp.870--877; Aschbacher--Smith C.1.32.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

include h

omit [Finite F] [CharP F 2] in
/-- SQTK passes to the actual quotient image through its two-group kernel. -/
theorem Input.component_image_sqtk :
    IsSQTK KnownSimple.IsKnownSimple (K.map (QuotientGroup.mk' (pCore 2 H))) := by
  have hk := h.sqtk.subgroup K
  have hq : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_,hk.isKGroup.quotient (pCore 2 K)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    rw [primeRank_quotient_eq_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup]
    exact hk.stronglyQuasithin p hp ho
  exact (IsSQTK.equiv (cComponentTwoCoreQuotientEquiv h.component)).mp hq

omit [CharP F 2] in
/-- The supplied matrix marking determines the quotient-component order. -/
theorem Input.component_image_card (hfour : Nat.card F = 4) :
    Nat.card (K.map (QuotientGroup.mk' (pCore 2 H))) = 979200 := by
  rw [← Nat.card_congr (cComponentTwoCoreQuotientEquiv h.component).toEquiv,
    Nat.card_congr h.quotientEquiv.toEquiv,
    Theory.SpecificGroups.SymplecticFour.card_sp, hfour]
  norm_num

/-- All short-group and conjugation-module clauses follow after these two
remaining source conclusions. No faithfulness or natural-module premise remains. -/
theorem Input.block_of_field_four_frattini_small (hfour : Nat.card F = 4)
    (hsmall : ⁅pCore 2 H,K⁆ ≤
      (frattini (pCore 2 H)).map (pCore 2 H).subtype ⊔ omegaCenterIn (pCore 2 H)) :
    IsSp4FourBlock K := by
  obtain ⟨hK,hB,hs,hq,hC⟩ := h.component_image_structure
  let := hK
  let := hB
  let := hs
  let := hq
  exact Sp4Four.block_of_frattini_small_ms K R h.component h.fitting h.characteristic
    h.radical.isPGroup h.radical_ne_bot h.radical.twoCore_le h.core_selfCentralizing
    h.omegaOrbit_centralizer (h.component_image_card hfour) hC
    h.component_image_sqtk hsmall

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
