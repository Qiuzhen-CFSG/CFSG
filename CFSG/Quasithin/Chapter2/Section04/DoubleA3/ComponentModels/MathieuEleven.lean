module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowFour
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import Theory.SpecificGroups.PSL2.CubicActorParameter
public import Theory.Mathieu.M11.Properties.FourNormalizer
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers

/-!
# The M₁₁ row in the original paired-cubic component inspection

All automorphisms of the actual M₁₁ carrier are inner. The source marked
action therefore absorbs the first cubic four-group into the component.
The original Sylow intersection normalizes that four-group. Intrinsically
its self-centralizer bounds every normalizing two-subgroup by eight, but
a Sylow two-subgroup of M₁₁ has order sixteen. This rules out the row.

The final wrapper obtains the marked 1.1.5 hypotheses from the original
maximal two-local setup. Source: Aschbacher–Smith, 2.4.32, p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The actual M₁₁ component row is incompatible with the paired-cubic source. -/
theorem SourceCentralizerGeometry.mathieu_eleven_component_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M11) : False := by
  have hz : center K = ⊥ := by
    apply (center K).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,Sporadic.Mathieu.m11_center_eq_bot,card_bot]
  obtain ⟨α,hα,_⟩ := (Chapter1.lemma_1_1_5_three_knownSimple hG _ _ _ _ h K hK).2.2
  obtain ⟨a,ha⟩ := Sporadic.Mathieu.automorphism_inner_of_equiv_m11 e α
  have hi : α ∈ (MulAut.conj : K →* MulAut K).range := ⟨a,ha.symm⟩
  have hU := g.first_module_le_component hG h K hK α hα hi hz
  let : K.Normal := g.component_normal_of_first_module h K hK hU
  obtain ⟨P,_,he,hc,_,hn,_⟩ := g.component_sylow_normal_four K hz hU
  let U := (c.U₁.subgroupOf (involutionCentralizer g.z₂)).subgroupOf K
  let : IsElementaryAbelian 2 U := he
  have hcardU : Nat.card U = 4 := hc
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hcardU,IsElementaryAbelian.exponent_eq_prime⟩
  have hb := Theory.PSL2.two_subgroup_normalizing_selfCentral_four_card_le_eight
    U P (Sporadic.Mathieu.m11_four_structure_of_equiv e U).1 P.isPGroup' hn
  have hcardP : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_congr e.toEquiv,Sporadic.Mathieu.m11_order]
    decide +kernel
  omega

/-- Construct the original marked involution hypotheses before excluding M₁₁. -/
theorem SourceCentralizerGeometry.mathieu_eleven_component_false_from_source
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (e : K ≃* Sporadic.Mathieu.M11) : False :=
  g.mathieu_eleven_component_false hG (g.lemma115 hG hM hTM hu).2 K hK e
end CFSG.Quasithin.Chapter2.DoubleA3
