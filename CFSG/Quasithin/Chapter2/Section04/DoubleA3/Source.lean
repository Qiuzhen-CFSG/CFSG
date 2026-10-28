module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FusionSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CrossNormalizerSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.NonCharacteristic
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.OriginalComponent
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.Source

/-!
# The original paired-cubic source after component recognition

The original maximum-local hypotheses and earlier single/linear exclusions
supply the actual normalizer reselection. Thus every elementary sixteen in
the original Thompson subgroup has at most six conjugates of the second
fixed involution. This is the guarded source37 conclusion, proved for the
same component and markings used by the cyclic-centralizer argument.

The terminal recognized-component endpoint derives the characteristic-two
exclusion, vanishing odd core, component layer, opposite-module noncentrality,
action markings, centralizer structure and fusion from their actual producers.
The remaining inputs are precisely source32's component absorption and
two-model conclusion, and the independent earlier linear/A5 exclusions used
in reselection.

Source: Aschbacher–Smith 2.4.30–37, printed pp.547–550.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

 theorem elementary_sixteen_fusion_from_source
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (e.block.map e.H.subtype) n → False)
    (hfive : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (b : SourceComponentGeometry d) (hz : b.z = g.z₂)
    (hs : b.s = c.s⁻¹) (hu₂ : (b.u:G) ∈ c.U₂)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype) :
    SourceElementarySixteenFusion b := by
  obtain ⟨hD,hR,_⟩ := g.component_centralizer_cyclic_four_from_source hG b hz hs hu₂ hLK
  have hQ : Nat.card (twoCore d.H)=16 := by simpa only [hD,one_mul] using c.core_card
  exact g.elementary_sixteen_fusion b hz hQ
    (g.cross_fusion_bound hG hM hTM hu hdelta hcounter hlinear hfive hST hpair hR)

 theorem false_of_component_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (e.block.map e.H.subtype) n → False)
    (hfive : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (b : SourceComponentGeometry d)
    (hz : b.z = g.z₂) (hs : b.s = c.s⁻¹) (hz₁ : (b.z₁:G) = g.z₁)
    (hu₂ : (b.u:G) ∈ c.U₂) (hx : (b.x:G) = c.x)
    (hP : (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
      (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype) : False := by
  have hf := g.elementary_sixteen_fusion_from_source hG hM hTM hu hdelta hcounter
    hlinear hfive hST hpair b hz hs hu₂ hLK
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  have ho := (g.original_component_catalogue hG hM hTM hu hn).1
  exact g.false_of_component_centralizer_normality b hz hs hz₁ hu₂ hx hP hLK hG.quasithin ho
    (g.component_centralizer_normality_of_geometry hG b hz hu₂ hLK) hf

 theorem false_of_component_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (e.block.map e.H.subtype) n → False)
    (hfive : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hVK : ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂))) : False := by
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  have ho := (g.original_component_catalogue hG hM hTM hu hn).1
  obtain ⟨b,hz,hs,hz₁,hu₂,hx,hKb,hP⟩ :=
    g.component_geometry_of_component_models (g.lemma115 hG hM hTM hu).2 ho K hK hLK hmodel hVK
  exact g.false_of_component_geometry hG hM hTM hu hdelta hcounter hlinear hfive hST hpair
    b hz hs hz₁ hu₂ hx hP (hKb.symm ▸ hLK)
/-- Source32's actual ordinary component, absorption and two-model recognition
feed the full original source33–37 contradiction. The noncentrality and layer
premises are discharged by their source producers. -/
 theorem false_of_recognized_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hdelta : (delta (Chapter1.He G) M).Nonempty)
    (hcounter : ¬ IsTheorem241Model G)
    (hlinear : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ∀ n, ChapterC.IsL2EvenBlock (e.block.map e.H.subtype) n → False)
    (hfive : ∀ e : MinimalBlockSetup M,
      (e.S : Subgroup e.H).map e.H.subtype < (T : Subgroup G) →
      ¬ ChapterC.IsAlternatingBlock (e.block.map e.H.subtype) 5)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
 : False := by
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  have ho := (g.original_component_catalogue hG hM hTM hu hn).1
  have h115 := (g.lemma115 hG hM hTM hu).2
  have hz : g.z₁ ∈ K.map (involutionCentralizer g.z₂).subtype :=
    hLK ((map_subtype_le _) g.first_mem)
  obtain ⟨a,ha,he⟩ := hz
  have hprod : g.z₁*g.z₂ = (a:G)*g.z₂ := congrArg (· * g.z₂) he.symm
  have hE := (source_component_structure g.z₂ g.P₂ M (g.z₁*g.z₂)
    h115 K hK a ha hprod ho).2.1
  have hVK := Noncentrality.source_second_not_central_component hG hu c g h115 K hK hE ho hLK hmodel
  exact g.false_of_component_models hG hM hTM hu hdelta hcounter hlinear hfive hST hpair
    K hK hLK hmodel hVK

end SourceCentralizerGeometry
end CFSG.Quasithin.Chapter2.DoubleA3
