module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.FamilyFusion
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentNormality
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentSource

/-!
# The paired-cubic terminal contradiction from the source components

The correlated component geometry gives its cyclic-four centralizer and
forces the core to have order sixteen. The single mixed-subgroup fusion
bound consequently controls the entire maximum-elementary family. The
proved component-normality, direct-factor and quotient-counting arguments
then give the original contradiction. The model endpoint consumes the
actual component of the literal fixed-involution centralizer.

Only the independently proved source32–35 component inputs and the first
mixed-subgroup normalizer calculation remain explicit here. No normality,
centralizer structure or pure-factor fusion assumption is retained.

Source: Aschbacher–Smith 2.4.32–37, printed pp.547–550.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
namespace SourceCentralizerGeometry
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)

 theorem false_of_component_geometry_and_cross_fusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (b : SourceComponentGeometry d)
    (hz : b.z = g.z₂) (hs : b.s = c.s⁻¹) (hz₁ : (b.z₁:G) = g.z₁)
    (hu : (b.u:G) ∈ c.U₂) (hx : (b.x:G) = c.x)
    (hP : (b.S₁ : Subgroup _).map (involutionCentralizer b.z).subtype =
      (g.P₂ : Subgroup _).map (involutionCentralizer g.z₂).subtype)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype)
    (hodd : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hcross : Nat.card {a : ((c.U₁ ⊔ c.V₂) ⊔ c.D : Subgroup G) //
      IsConj g.z₂ (a:G)} ≤6) : False := by
  have hD := (g.component_centralizer_cyclic_four_from_source hG b hz hs hu hLK).1
  have hQ : Nat.card (twoCore d.H)=16 := by simpa only [hD,one_mul] using c.core_card
  exact g.false_of_component_centralizer_normality b hz hs hz₁ hu hx hP hLK hG.quasithin
    hodd (g.component_centralizer_normality_of_geometry hG b hz hu hLK)
    (g.elementary_sixteen_fusion b hz hQ hcross)

 theorem false_of_component_models_and_cross_fusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : Theory.GroupTheory.IsComponent (involutionCentralizer g.z₂) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hVK : ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂)))
    (hcross : Nat.card {a : ((c.U₁ ⊔ c.V₂) ⊔ c.D : Subgroup G) //
      IsConj g.z₂ (a:G)} ≤6) : False := by
  obtain ⟨b,hz,hs,hz₁,hu,hx,hKb,hP⟩ :=
    g.component_geometry_of_component_models h ho K hK hLK hmodel hVK
  exact g.false_of_component_geometry_and_cross_fusion hG b hz hs hz₁ hu hx hP
    (hKb.symm ▸ hLK) ho hcross
end SourceCentralizerGeometry
end CFSG.Quasithin.Chapter2.DoubleA3
