module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.FullSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.OriginalInputs
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# Original overgroup equality without a universal embedding premise

The source 1.2.4 theorem constructs a containing component in G₁. Orders of
the three actual surviving quotients leave only a possible A₆ section in an
L₄(2) component. Original 13.8.26 makes the same local quotient L/O₂(L)
ordinary in the first case, whereas 13.8.25 gives its central triple cover
in the second. Comparing their centers excludes this remaining case.
Equality in G₁/O₂(G₁) lifts through the common Sylow to K=K₁ and G₁=H=KT.

This uses the source local quotient conclusions; it asserts no exclusion of
abstract A₆ embeddings in L₄(2). `SourceAssembly.Original` supplies the
preceding component and field reductions to this argument.
Source: Aschbacher–Smith, 1.2.4 and 13.8.25–27, printed pp.505,960–963.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open CriticalGeometry SourceCompletion
open FieldComponents.HigherFieldReduction.ExternalModules
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem survivor_card {X : Type*} [Group X] (h : Overgroup.Survivor X) :
    Nat.card X = 360 ∨ Nat.card X = 20160 ∨ Nat.card X = 6048 := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · right; left
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    rw [Nat.card_congr e.toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    exact hc
  · obtain ⟨e⟩ := h
    right; right
    rw [Nat.card_congr e.toEquiv]
    exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)

omit [IsElementaryAbelian 2 (Source.UH H V₃)] in
private theorem stars_equal_unless_six_in_four {X : Type*} [Group X] [Finite X]
    {B C : Subgroup X} (hle : B ≤ C)
    (hB : Overgroup.Survivor (B ⧸ pCore 2 B)) (hC : Overgroup.Survivor C) :
    B = C ∨ Nat.card (B ⧸ pCore 2 B) = 360 ∧ ClassicalGroup.IsPSL C 4 2 := by
  have hd := (card_quotient_dvd_card (pCore 2 B)).trans (card_dvd_of_le hle)
  have hqle : Nat.card (B ⧸ pCore 2 B) ≤ Nat.card B :=
    Nat.le_of_dvd Nat.card_pos (card_quotient_dvd_card (pCore 2 B))
  rcases hC with hC | hC | hC
  · have he : Nat.card C = 360 := by
      obtain ⟨e⟩ := hC
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    rcases survivor_card hB with hs | hs | hs
    · exact Or.inl (eq_of_le_of_card_ge hle (by omega))
    · rw [hs, he] at hd; norm_num at hd
    · rw [hs, he] at hd; norm_num at hd
  · have he : Nat.card C = 20160 := by
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hC
      have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      rw [hF] at hc
      norm_num [Fin.prod_univ_succ] at hc
      exact (Nat.card_congr e.toEquiv).trans hc
    rcases survivor_card hB with hs | hs | hs
    · exact Or.inr ⟨hs, hC⟩
    · exact Or.inl (eq_of_le_of_card_ge hle (by omega))
    · rw [hs, he] at hd; norm_num at hd
  · have he : Nat.card C = 6048 := by
      obtain ⟨e⟩ := hC
      rw [Nat.card_congr e.toEquiv]
      exact Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)
    rcases survivor_card hB with hs | hs | hs
    · rw [hs, he] at hd; norm_num at hd
    · rw [hs, he] at hd; norm_num at hd
    · exact Or.inl (eq_of_le_of_card_ge hle (by omega))

/-- Prove relative component normality and G₁=H=KT using the source local quotients. -/
theorem original_overgroup_equalities
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (localEarlier : Solvable.EarlierLocalInputs (G := G))
    (facts : UniformComponentFacts L (sourceOne L T V₁) T G₁ M)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    (K.subgroupOf G₁).IsCComponent ∧ (K.subgroupOf G₁).Normal ∧
      G₁ = H ∧ H = K ⊔ (T : Subgroup G) := by
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.line_card)
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, card_bot] at hc
    contradiction
  have hb : V₁ ≤ sourceOne L T V₁ ⊔ (T : Subgroup G) :=
    ((d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)).trans
      (localNaturalSetup d).chosen.le_sylow).trans le_sup_right
  have hG := Overgroup.ambient_mem_Hz hHz hne hp hb d.first_normalizer.le
  have hQ := ChapterE.Structure.sqtk_two_quotient
    (d.counterexample.qtke.twoLocal_sqtk ⟨V₁, hne, hp, d.first_normalizer⟩)
    (pCore 2 G₁) pCore_isPGroup
  obtain ⟨K₁, hK₁G, hK₁, hKK₁, hn⟩ :=
    AlternatingAndLinear.LinearReduction.OriginalSource.exists_component_overgroup_source
      hHz hKH hK (facts.normal hHz hKH hK) hQ
  let e := Overgroup.quotientStarQuotientEquiv (hKH.trans hHz.2.1)
  let e₁ := Components.componentStarEquiv G₁ K₁ hK₁G hK₁
  have hs := (Overgroup.surviving_quotient facts hHz hKH hK).of_equiv e
  have hl := (Overgroup.surviving_quotient facts hG hK₁G hK₁).of_equiv e₁
  have he : Source.starImage G₁ K = Source.starImage G₁ K₁ := by
    rcases stars_equal_unless_six_in_four (map_mono (comap_mono hKK₁)) hs hl with he | ⟨hcard, h4⟩
    · exact he
    have cardK : Nat.card (K ⧸ pCore 2 K) = 360 :=
      (Nat.card_congr e.toEquiv).trans hcard
    have h6 : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
      rcases Overgroup.surviving_quotient facts hHz hKH hK with h6 | h4' | hg
      · exact h6
      · obtain ⟨F, _, _, hF, ⟨f⟩⟩ := h4'
        have hc' := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
        rw [hF] at hc'
        norm_num [Fin.prod_univ_succ] at hc'
        rw [Nat.card_congr f.toEquiv, hc'] at cardK
        contradiction
      · obtain ⟨f⟩ := hg
        have hc := Atlas.G2.DerivedEvenOrder.card_derived_binary (F := ZMod 2) (by simp)
        rw [Nat.card_congr f.toEquiv, hc] at cardK
        contradiction
    obtain ⟨eK⟩ := h6
    obtain ⟨_, _, _, ⟨eL⟩, _⟩ := six_source_alternative d earlier localEarlier hHz hF9
      hKH hK (facts.normal hHz hKH hK) (facts.join_eq hHz hKH hK)
      hfit hUK hcentral hcomm eK ρ hρ
    have hcover := (facts.binaryReduction hG hK₁G hK₁ (by decide : 3 ≤ 4)
      (by decide : 4 ≤ 5) (h4.of_mulEquiv e₁)).2.1
    obtain ⟨z⟩ := hcover.2.1
    have hz := (Nat.card_congr z.toEquiv).trans (Nat.card_zmod 3)
    have hez := Nat.card_congr (centerCongr eL).toEquiv
    rw [alternatingGroup.center_eq_bot (by simp), card_bot, hz] at hez
    contradiction
  have hKeq := Overgroup.component_eq_of_star_eq (le_sup_right.trans hHz.1.2)
    hHz.2.1 hKH hK hK₁G hK₁ hKK₁ he
  subst K₁
  exact ⟨hK₁, hn, (facts.join_eq hG (hKH.trans hHz.2.1) hK₁).trans
    (facts.join_eq hHz hKH hK).symm, facts.join_eq hHz hKH hK⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
