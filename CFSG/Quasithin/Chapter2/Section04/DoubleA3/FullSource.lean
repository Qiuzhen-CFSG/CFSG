module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.Source32
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.MathieuCover

/-!
# The original paired-cubic component and source contradiction

The literal marked 1.1.5 catalogue is reduced to A₆ or PSL₃(2), with the
first cubic block contained in the selected ordinary component. The binary
Mathieu exception is excluded by its actual quotient action. Source33–35
then construct the normal A₆ component and all original actor markings.
The completed source36–37 consumer excludes the original paired-cubic case.

The only callbacks concern the independent earlier linear and A₅ block
cases used in source31 and source37 reselection. No component recognition,
model action, noncentrality or fusion hypothesis is added to the source.

Source: Aschbacher–Smith 2.4.27–37, printed pp.546–550.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- The source32 recognition and whole-block absorption for the actual
ordinary component selected by the original 1.1.5 marking. -/
theorem SourceCentralizerGeometry.recognized_component_from_source
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hn : involutionCentralizer g.z₂ ∉ Chapter1.He G) :
    ∃ K : Subgroup (involutionCentralizer g.z₂), IsComponent (involutionCentralizer g.z₂) K ∧
      d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
      (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL)) := by
  obtain ⟨ho,K,hK,_,_,α,hα,hm⟩ := g.original_component_catalogue hG hM hTM hu hn
  rcases g.model_action_source32_or_binary_mathieu hG hM hTM hu hST hpair K hK α hα ho hm
      with hgood | ⟨hk,he⟩
  · exact ⟨K,hK,hgood⟩
  · exact (g.binary_mathieu_twentyTwo_component_false hG hM hTM hu hST hpair K hK hk he.some).elim

/-- Source32–35 preserve the selected involutions, actors, component
inclusion and common Sylow subgroup in the final A₆ geometry. -/
theorem SourceCentralizerGeometry.component_geometry_from_source
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (hn : involutionCentralizer g.z₂ ∉ Chapter1.He G) :
    ∃ b : SourceComponentGeometry d, b.z = g.z₂ ∧ b.s = c.s⁻¹ ∧
      (b.z₁ : G) = g.z₁ ∧ (b.u : G) ∈ c.U₂ ∧ (b.x : G) = c.x ∧
      (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
        (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype ∧
      d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype := by
  obtain ⟨K,hK,hLK,hmodel⟩ := g.recognized_component_from_source hG hM hTM hu hST hpair hn
  have ho := (g.original_component_catalogue hG hM hTM hu hn).1
  have h115 := (g.lemma115 hG hM hTM hu).2
  have hz : g.z₁ ∈ K.map (involutionCentralizer g.z₂).subtype :=
    hLK ((map_subtype_le _) g.first_mem)
  obtain ⟨a,ha,he⟩ := hz
  have hprod : g.z₁*g.z₂ = (a:G)*g.z₂ := congrArg (· * g.z₂) he.symm
  have hE := (source_component_structure g.z₂ g.P₂ M (g.z₁*g.z₂)
    h115 K hK a ha hprod ho).2.1
  obtain ⟨b,hz,hs,hz₁,hu₂,hx,hKb,hP⟩ :=
    Noncentrality.source_component_geometry hG hu c g h115 K hK hE ho hLK hmodel
  exact ⟨b,hz,hs,hz₁,hu₂,hx,hP,hKb.symm ▸ hLK⟩

end CFSG.Quasithin.Chapter2.DoubleA3
namespace CFSG.Quasithin.Chapter2
open DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The original paired-cubic source constructs its actual component
geometry; the earlier block exclusions are used only by source31. -/
theorem MinimalBlockSetup.paired_cubic_component_geometry
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
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
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) :
    Nonempty (SourceComponentGeometry d) := by
  obtain ⟨c⟩ := d.paired_cubic_coordinates hG T hM hTM hu hST hpair hL
  obtain ⟨g⟩ := c.exists_centralizer_geometry hG hM hTM hu hST hpair
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  obtain ⟨b,_⟩ := g.component_geometry_from_source hG hM hTM hu hST hpair hn
  exact ⟨b⟩

/-- The original paired-cubic case is impossible after the independent
linear and A₅ cases have been excluded for the reselected blocks. -/
theorem MinimalBlockSetup.paired_cubic_source_false
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
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
    (hL : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 3) : False := by
  obtain ⟨c⟩ := d.paired_cubic_coordinates hG T hM hTM hu hST hpair hL
  obtain ⟨g⟩ := c.exists_centralizer_geometry hG hM hTM hu hST hpair
  have hn := (g.not_He_of_prior_cases hG hM hTM hu hdelta hcounter hlinear hfive hST hpair).2
  obtain ⟨b,hz,hs,hz₁,hu₂,hx,hP,hLK⟩ :=
    g.component_geometry_from_source hG hM hTM hu hST hpair hn
  exact g.false_of_component_geometry hG hM hTM hu hdelta hcounter hlinear hfive hST hpair
    b hz hs hz₁ hu₂ hx hP hLK

end CFSG.Quasithin.Chapter2
