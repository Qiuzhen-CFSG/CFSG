module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.ModelConstruction
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.CoreTransport
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSource

/-!
# The original paired-cubic noncentrality theorem

Assuming that the opposite four-group centralizes the selected component
produces the faithful paired binary linear model. Its original involution
marks satisfy all three ambient nonfusion relations, contradicting the two
index-two transfers. Thus the actual opposite module acts nontrivially on
the actual component. The preceding selection and layer identification are
exactly the source32/33 inputs, with their literal centralizer maps retained.

Source: Aschbacher--Smith, Lemma 2.4.34, printed p.548.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
variable {G : Type*} [Group G] [Finite G]
variable {M : Subgroup G} {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The original opposite four-group does not centralize the component
selected in 2.4.32. This supplies the noncentrality input of 2.4.35. -/
theorem source_second_not_central_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hE : K = componentLayer (involutionCentralizer g.z₂))
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL)) :
    ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂)) := by
  intro hc
  let := hG.simple
  have : K.Normal := by rw [hE]; infer_instance
  have hUR : c.U₂ ≤ sourceR d := c.baumann ▸ c.second.module_le
  have hRH : sourceR d ≤ involutionCentralizer g.z₂ := by
    intro r hr
    exact mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  have hcomm : c.U₂ ≤ centralizer (K.map (involutionCentralizer g.z₂).subtype : Set G) := by
    intro u hu k hk
    obtain ⟨v,hv,rfl⟩ := hk
    exact congrArg Subtype.val
      (hc (show (⟨u,hRH (hUR hu)⟩ : involutionCentralizer g.z₂) ∈
        c.U₂.subgroupOf (involutionCentralizer g.z₂) from hu) v hv)
  obtain ⟨m⟩ := source_paired_embedding hG hu c g K hK hE ho hfirst hmodel hcomm
  exact m.false_of_source (Subgroup.index_ne_two_of_nonabelian_simple hG.nonabelian) h hK


/-- The proved 2.4.34 noncentrality supplies the literal component geometry
used by 2.4.35, retaining the source's involutions, actors and Sylow subgroup. -/
theorem source_component_geometry
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hE : K = componentLayer (involutionCentralizer g.z₂))
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL)) :
    ∃ b : SourceComponentGeometry d, b.z = g.z₂ ∧ b.s = c.s⁻¹ ∧
      (b.z₁ : G) = g.z₁ ∧ (b.u : G) ∈ c.U₂ ∧ (b.x : G) = c.x ∧
      b.K.map (involutionCentralizer b.z).subtype = K.map (involutionCentralizer g.z₂).subtype ∧
      (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
        (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype := by
  have : K.Normal := by rw [hE]; infer_instance
  exact g.component_geometry_of_two_models K hfirst hmodel
    (source_second_not_central_component hG hu c g h K hK hE ho hfirst hmodel)

end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
