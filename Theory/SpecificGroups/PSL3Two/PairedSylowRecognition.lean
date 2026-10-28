module

public import Theory.SpecificGroups.PSL3Two.BorelCenterNormalizer
public import Theory.GroupTheory.PairedInvolutiveExtension.Geometry
public import Theory.GroupTheory.PairedInvolutiveExtension.Subgroups

/-!
# Standard paired Sylow recognition for SL₃(2)

The Borel product in the normal base has normalizer equal to its extension
by the two actor involutions. Its order 256 is the full two-part of the
paired model order 112896. Consequently every Sylow two-subgroup containing
the Borel product is this standard paired subgroup. The only nonidentity
central element of either Borel factor is the specified highest-root
involution, retaining the central marks used by the source application.

Source: Aschbacher--Smith, proof of 2.4.34, printed p.548 of the
1 March 2004 manuscript.
-/

@[expose] public section
namespace Matrix.PSL3Two.PairedSylowRecognition
open Subgroup Theory.GroupTheory.PairedInvolutiveExtension MarkedAutomorphisms
abbrev StandardModel := Model diagram diagram_involutive
theorem diagram_stable_borel : ∀ a ∈ borelSL, diagram a ∈ borelSL :=
  fun a ha => (PairedGraphInputs.diagram_mem_borel_iff a).mpr ha
abbrev standardPaired : Subgroup StandardModel :=
  subgroup diagram diagram_involutive borelSL diagram_stable_borel
theorem card_standardPaired : Nat.card standardPaired = 256 := by
  rw [card_subgroup,card_borelSL]
  decide
theorem card_standardModel : Nat.card StandardModel = 112896 := by
  rw [SemidirectProduct.card,Nat.card_prod,Nat.card_prod,card_SL,card_bit]
/-- The standard Borel-pair extension is a Sylow two-subgroup. -/
def standardSylow : Sylow 2 StandardModel := Sylow.ofCard standardPaired (by
  rw [card_standardPaired,card_standardModel]
  decide +kernel)
/-- The Borel product is Sylow in the normal base. -/
def borelProductSylow : Sylow 2 (SL × SL) := Sylow.ofCard (borelSL.prod borelSL) (by
  rw [Nat.card_congr (prodEquiv borelSL borelSL).toEquiv, Nat.card_prod,card_borelSL,
    Nat.card_prod,card_SL]
  decide +kernel)
@[simp] theorem standardSylow_coe : (standardSylow : Subgroup StandardModel) = standardPaired := rfl
abbrev standardBase : Subgroup StandardModel := baseSubgroup diagram diagram_involutive borelSL

/-- The Borel-pair extension is the full normalizer of the base Borel product. -/
theorem normalizer_standardBase : normalizer (standardBase : Set StandardModel) = standardPaired :=
  normalizer_baseSubgroup diagram diagram_involutive borelSL diagram_stable_borel
    BorelCenterNormalizer.normalizer_borel

/-- Containing the base Borel product determines the full Sylow subgroup. -/
theorem sylow_eq_standard_of_base_le (S : Sylow 2 StandardModel)
    (hbase : standardBase ≤ (S : Subgroup StandardModel)) : (S : Subgroup StandardModel) = standardPaired := by
  have hn : (S : Subgroup StandardModel) ≤ normalizer (standardBase : Set StandardModel) :=
    le_normalizer_baseSubgroup_of_le diagram diagram_involutive borelSL borelProductSylow rfl
      S S.isPGroup' hbase
  rw [normalizer_standardBase] at hn
  exact (S.is_maximal' standardSylow.isPGroup' hn).symm

/-- Every selected nontrivial central Borel mark is the highest-root involution. -/
theorem highestRoot_eq_of_center_ne_one (z : borelSL) (hz : z ∈ center borelSL) (hne : z ≠ 1) :
    (z : SL) = PairedGraphInputs.highestRoot := by
  rcases (BorelCenterNormalizer.center_mem_iff z).mp hz with h | h
  · exact False.elim (hne (Subtype.ext h))
  · exact h
end Matrix.PSL3Two.PairedSylowRecognition
