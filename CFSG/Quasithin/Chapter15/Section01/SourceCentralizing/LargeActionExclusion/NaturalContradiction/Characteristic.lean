module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.NaturalContradiction.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.SourceClassifications

/-!
# The precise C.1.34 step in original 15.1.29

For the actual K=⟨O²(P₀),O²(P₂)⟩ and R=O₂(P₂), assume the rank-two
local structure and its centralizer-core identification have been proved.
If no nontrivial characteristic subgroup of R were normal in KR, these
data would give a complete SmallMSPair. C.1.34's block outcome is excluded
by the two noncentral chief layers. Its three centralizer-core inequalities
contradict the identified core, and its central-omega outcome would make R
equal to O₂(KR). Thus a characteristic subgroup exists, with normality
relative to KR throughout.

The rank-two input and the earlier C.1.34 classification remain explicit.
This module proves their implication, not either source input.

Source: Aschbacher--Smith, C.1.31--34, pp.135--137, and 15.1.29, p.1104.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Only the binary C.1.34 implication is needed here, not the independent
C.1.32 classification contained in the other field of `EarlierMSClassifications`. -/
def NaturalParabolicMSClassification (G : Type u) [Group G] : Prop :=
  ∀ L R : Subgroup G, SmallMSPair KnownSimple.IsKnownSimple L R →
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    ∀ S : Subgroup G, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
      ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
        MSModuleAlternatives L R S 1 (ZMod 2) e

/-- Specialization of exactly the existing `linearThree` field. -/
theorem naturalParabolicMSClassification_of_earlier
    (earlier : EarlierMSClassifications.{u} KnownSimple.IsKnownSimple) :
    NaturalParabolicMSClassification G := by
  intro L R hms he S hS hRS
  exact earlier.linearThree G L R hms 1 (by decide) (ZMod 2) (by simp) he S hS hRS

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The rank-two geometric input to C.1.34, before imposing MS3.
In particular no characteristic-subgroup witness is included. The core
identity concerns Ω₁Z(S), exactly as in C.1.34, and must be established
from the original marked centralizer in 15.1.29. -/
structure NaturalRankTwoInput {d : CaseIComponentData T M Mc V}
    (p : NaturalParabolics d) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple (p.K ⊔ p.Q2 : Subgroup G)
  fitting : generalizedFitting (p.K ⊔ p.Q2 : Subgroup G) =
    pCore 2 (p.K ⊔ p.Q2 : Subgroup G)
  product : ∀ g ∈ p.K ⊔ p.Q2, ∃ k ∈ p.K, ∃ r ∈ p.Q2, k * r = g
  component : (p.K.subgroupOf (p.K ⊔ p.Q2)).IsCComponent
  parabolic_proper : p.P2 < p.K ⊔ p.Q2
  parabolic_index : (p.P2.subgroupOf (p.K ⊔ p.Q2)).index = 7
  model : Nonempty ((p.K ⧸ pCore 2 p.K) ≃*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
  sylow : Chapter1.IsSylowIn 2 d.S (p.K ⊔ p.Q2)
  core_le_sylow : p.Q2 ≤ d.S
  centralizer_core : p.Q2 =
    ((p.K ⊔ p.Q2) ⊓ centralizer (SourceInterface.omegaCenterIn d.S : Set G)).pCoreIn 2
  radical_not_core : p.Q2 ≠ (p.K ⊔ p.Q2).pCoreIn 2
  not_linear_block : ¬ ChapterC.IsSL3EvenBlock p.K 1

namespace NaturalRankTwoInput
variable {d : CaseIComponentData T M Mc V} {p : NaturalParabolics d}

/-- The full SL₃(2) identification supplies the central-quotient version
of MS1 as well: the binary model has trivial center and is perfect. -/
theorem rankTwo (b : NaturalRankTwoInput p) : SmallRankTwoQuotient p.K := by
  obtain ⟨e⟩ := b.model
  have hz : center (p.K ⧸ pCore 2 p.K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact e.map_eq_one_iff.mp
      (Matrix.PSL3Two.center_eq_bot.le ((centerCongr e ⟨x,hx⟩).property))
  have he : centralPreimage (pCore 2 p.K) = pCore 2 p.K := by
    change (center (p.K ⧸ pCore 2 p.K)).comap (QuotientGroup.mk' _) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  let := Atlas.sl_perfect 3 (by decide) (F := ZMod 2)
  apply Or.inl
  exact ⟨((QuotientGroup.quotientMulEquivOfEq he).trans e).trans (topEquiv.symm.trans
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top.symm))⟩

/-- MS2(a) uses the actual P₂ and its two-core, at its source index seven. -/
theorem radical (b : NaturalRankTwoInput p) : MSOddIndex p.K p.Q2 := by
  refine ⟨p.P2,b.parabolic_proper,?_,rfl⟩
  rw [b.parabolic_index]
  decide

/-- The central-omega alternative would collapse the parabolic radical
to the rank-two core, contrary to the actual parabolic quotient. -/
theorem omega_not_central (b : NaturalRankTwoInput p) :
    ¬ SourceInterface.omegaCenterIn d.S ≤ SourceInterface.centerIn (p.K ⊔ p.Q2) := by
  intro hc
  have hcen : p.K ⊔ p.Q2 ≤ centralizer (SourceInterface.omegaCenterIn d.S : Set G) := by
    apply le_centralizer_iff.mp
    intro z hz g hg
    obtain ⟨a,ha,rfl⟩ := hc hz
    exact congrArg Subtype.val ((mem_center_iff.mp ha) ⟨g,hg⟩)
  exact b.radical_not_core (b.centralizer_core.trans (by rw [inf_eq_left.mpr hcen]))

/-- All five C.1.34 outcomes are used, with their literal quotient and
centralizer conventions. Only the `linearThree` field is consumed. -/
theorem exists_characteristic_normal (b : NaturalRankTwoInput p)
    (hMS : NaturalParabolicMSClassification G) :
    ∃ C : Subgroup p.Q2, C.Characteristic ∧ C ≠ ⊥ ∧
      ((C.map p.Q2.subtype).subgroupOf (p.K ⊔ p.Q2)).Normal := by
  classical
  by_contra hnone
  have hchar : MSNoCharacteristicNormal p.K p.Q2 := by
    intro C hC hn
    by_contra hne
    exact hnone ⟨C,hC,hne,hn⟩
  have hms : SmallMSPair KnownSimple.IsKnownSimple p.K p.Q2 := {
    finite := inferInstance
    sqtk := b.sqtk
    fitting := b.fitting
    product := b.product
    component := b.component
    rankTwo := b.rankTwo
    radical := b.radical
    characteristic := hchar }
  obtain ⟨e,he⟩ := hMS p.K p.Q2 hms b.model d.S b.sylow b.core_le_sylow
  rcases he with h1 | h2 | h3 | h4 | h5
  · exact b.not_linear_block h1.2.1
  · exact h2.2 b.centralizer_core
  · exact h3.2.2 b.centralizer_core
  · exact h4.2.2.2.2.2.2.2.2.2 b.centralizer_core
  · exact b.omega_not_central h5.2.2.2.1

end NaturalRankTwoInput
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
