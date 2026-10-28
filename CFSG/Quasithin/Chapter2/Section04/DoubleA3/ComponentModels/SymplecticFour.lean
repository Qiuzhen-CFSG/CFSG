module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSylowR
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FrattiniBound
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.AlternatingSix
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints
public import Theory.SpecificGroups.SymplecticFour.Sylow.FrattiniBound
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The symplectic row in the original paired cubic component inspection

For a nonbinary field, the marked product z₁z₂ fixes a full Sylow subgroup
of the actual component pointwise, so its automorphism is inner. The
original cubic four-group then lies in the centerless component and makes
that component normal in the second involution centralizer.

The second cubic module's original movement places this normal component's
full Sylow intersection in R. The source calculation gives |Φ(R)| = 4,
whereas a Sylow subgroup of Sp₄(q) has Frattini subgroup of order q².
Functoriality of Frattini subgroups of finite two-groups therefore excludes
every q > 2, including q = 4. The actual derived binary matrix carrier is
A₆, and the completed A₆ absorption theorem puts the literal first cubic
block in the component.

The final wrapper constructs the 1.1.5 premise from the original ambient
T and the same marked involutions. No additional Sylow placement or model
normalizer hypothesis is assumed.

Source: Aschbacher–Smith, the inspection preceding 2.4.32, printed p.547.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem symplectic_center_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : center B = ⊥) : center A = ⊥ := by
  apply eq_bot_iff.mpr
  intro a ha
  have hb := (centerCongr e ⟨a,ha⟩).property
  change e a ∈ center B at hb
  rw [h,mem_bot] at hb
  exact e.injective (hb.trans e.map_one.symm)

private theorem component_sylow_frattini_bound
    (g : SourceCentralizerGeometry c)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hzK : center K = ⊥) :
    ∃ Q : Sylow 2 K, Nat.card (frattini Q) ≤ 4 := by
  let H := involutionCentralizer g.z₂
  obtain ⟨Q,hQ⟩ := g.P₂.exists_subgroupOf_eq_of_normal K
  let i : K →* G := H.subtype.comp K.subtype
  have hi : Function.Injective i := H.subtype_injective.comp K.subtype_injective
  let QG := (Q : Subgroup K).map i
  have hQR : QG ≤ sourceR d := by
    apply le_trans (show QG ≤ K.map H.subtype ⊓ (g.P₂ : Subgroup H).map H.subtype from ?_)
      (g.component_sylow_le_sourceR K hzK)
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨mem_map_of_mem H.subtype q.property,mem_map_of_mem H.subtype ?_⟩
    rw [hQ] at hq
    exact hq
  have hPhi := c.subgroup_frattini_card_le QG hQR (Q.isPGroup'.map i)
  let eQ : Q ≃* QG := (Q : Subgroup K).equivMapOfInjective i hi
  have he : Nat.card (frattini Q) = Nat.card (frattini QG) := by
    rw [←frattini_map_equiv eQ,card_map_of_injective eQ.injective]
  exact ⟨Q,he ▸ hPhi⟩

/-- In the actual paired cubic source, the symplectic component is binary. -/
theorem SourceCentralizerGeometry.derived_symplectic_four_component_six
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hm : ComponentRefinement.LieType.IsDerivedSymplecticFour K) :
    Nonempty (K ≃* AlternatingSix.ShadowLocal.A6) := by
  obtain ⟨n,hn,F,_,_,hF,⟨e⟩⟩ := hm
  by_cases h1 : n = 1
  · exact ⟨e.trans (Binary.derivedEquivAlternatingSix
      (by simpa only [h1,pow_one] using hF))⟩
  · have hn' : 1 < n := by omega
    let : CharP F 2 := EvenProjective.charTwo_of_card hF
    have hq : 2 < Nat.card F := by
      rw [hF]
      have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    let eK := e.trans (derivedEquivFull_of_card_gt_two hq)
    have hzK : center K = ⊥ := symplectic_center_transport eK EvenProjective.center_eq_bot
    obtain ⟨_,α,P,hα,hmark,_⟩ := h.component_inputs K hK
    have hi := FrattiniBound.fixing_sylow_inner_of_equiv hF hn' eK P α hmark.fixes
    have hU := g.first_module_le_component hG h K hK α hα hi hzK
    let : K.Normal := g.component_normal_of_first_module h K hK hU
    obtain ⟨Q,hPhi⟩ := component_sylow_frattini_bound g K hzK
    exact (FrattiniBound.not_equiv_of_small_sylow_frattini hF hn' eK Q hPhi).elim

/-- The retained model also contains the literal first cubic block. -/
theorem SourceCentralizerGeometry.derived_symplectic_four_component_absorbs_first_block
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hm : ComponentRefinement.LieType.IsDerivedSymplecticFour K) :
    Nonempty (K ≃* AlternatingSix.ShadowLocal.A6) ∧ K.Normal ∧
      d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype := by
  obtain ⟨e⟩ := g.derived_symplectic_four_component_six hG h K hK hm
  exact ⟨⟨e⟩,g.alternating_six_component_absorbs_first_block hG K hK e⟩

/-- Construct the marked 1.1.5 input from the original ambient hypotheses. -/
theorem SourceCentralizerGeometry.derived_symplectic_four_from_original
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hm : ComponentRefinement.LieType.IsDerivedSymplecticFour K) :
    Nonempty (K ≃* AlternatingSix.ShadowLocal.A6) ∧ K.Normal ∧
      d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype :=
  g.derived_symplectic_four_component_absorbs_first_block hG (g.lemma115 hG hM hTM hu).2 K hK hm

end CFSG.Quasithin.Chapter2.DoubleA3
