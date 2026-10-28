module
public import CFSG.Quasithin.Chapter13.Section07.ComponentWholeSource
public import CFSG.Quasithin.Chapter13.Section07.TildeOffenders
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.Kernel
public import Theory.Representation.BinaryConjugationSection.Projection
public import Theory.Representation.BinaryOffender.IrreducibleCentralLift

/-!
# Irr⁺ on the original tilde module

The actual coordinate maps induce the projection from U_H/V₁ to U_H/U₀.
Centrality of the selected component on U₀ puts this projection's kernel
in its fixed space. Perfectness then lifts Irr⁺ from the whole plus module
to the component commutator in the tilde module. The final application
constructs the faithful tilde action and retains both original offenders.

This discharges 13.7.16(3) from the earlier source packet and the precise
13.7.16(2) centrality conclusion, which remains a separate source input.
Source: Aschbacher–Smith, 13.7.16, printed p.944.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

/-- The fixed-layer centrality input transfers the original Irr⁺ module on
`U_H/U₀` back to the literal quotient `U_H/V₁`. -/
theorem component_irrPlus_of_fixed_layer_central
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {W W₀ : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup W₀] [Module (ZMod 2) W₀]
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W)
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (τ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) W₀)
    (s : BinaryConjugationSection D.H D.UH (PlusAction.fixedLayer D)
      (τ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (K : Subgroup D.H)
    (hK : IsComponent (D.H ⧸ pCore 2 D.H) (K.map (QuotientGroup.mk' (pCore 2 D.H))))
    (hcentral : K.map D.H.subtype ≤ centralizer (PlusAction.fixedLayer D : Set G))
    (hi : IsIrrPlus τ (K.map (QuotientGroup.mk' (pCore 2 D.H))) ⊤) :
    IsIrrPlus ρ (K.map (QuotientGroup.mk' (pCore 2 D.H)))
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 D.H)))) := by
  let π := QuotientGroup.mk' (pCore 2 D.H)
  let J := K.map π
  let : IsQuasisimple J := hK.2
  obtain ⟨p, hp, hpcoord, hpker⟩ :=
    BinaryConjugationSection.exists_projection
      D.H D.H D.UH D.V₁ (PlusAction.fixedLayer D) le_rfl
      (PlusAction.point_le_fixedLayer h)
      π π (QuotientGroup.mk'_surjective _) (MonoidHom.id _)
      (by intro k; rfl) ρ τ c s
  have he : ∀ k : J, ∀ v, p.toLinearMap (ρ k v) = τ k (p.toLinearMap v) := by
    intro k v
    exact LinearMap.congr_fun (p.isIntertwining' k) v
  have hker : p.toLinearMap.ker ≤ fixedSpace ρ J := by
    rw [hpker]
    intro v hv k
    obtain ⟨k', hk', heq⟩ := k.property
    have hc : ⁅K.map D.H.subtype, PlusAction.fixedLayer D⁆ ≤ D.V₁ :=
      (commutator_eq_bot_iff_le_centralizer.mpr hcentral).le.trans bot_le
    have hh := c.fixed_on_imageSpace_of_commutator_le
      (K.map D.H.subtype) (PlusAction.fixedLayer D) hc k'
      (mem_map_of_mem D.H.subtype hk') v hv
    change ρ (π k') v = v at hh
    change ρ k.val v = v
    rwa [heq] at hh
  exact IsIrrPlus.of_central_surjection ρ τ J p.toLinearMap hp he hker hi


variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- Original 13.7.16(3), on the same selected source component and quotient.
The original 13.7.16(2) centrality conclusion is the only later premise. -/
theorem source_tilde_component_irrPlus
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) E)
    (c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hcentral : K.map H.subtype ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G)) :
    IsIrrPlus ρ (K.map (QuotientGroup.mk' (pCore 2 H)))
      (subspaceCommutator ρ ⊤ (K.map (QuotientGroup.mk' (pCore 2 H)))) := by
  have hi := (source_plus_component_irrPlus_and_actor d h hU hV hne g hs hout
    σ s B hB hBA K hK hk hcomm).1
  have hg := source_plus_component_whole d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm
  rw [hg] at hi
  exact component_irrPlus_of_fixed_layer_central h ρ c σ s K hK hcentral hi

/-- Construct the faithful literal tilde action, both original offenders and
Irr⁺ for the same selected component. -/
theorem exists_source_tilde_component_irrPlus
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (g : (L ⊔ (T : Subgroup G) : Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) g)^2 = 1)
    (hout : ¬ conjugate V₁ (g : G) ≤ Section08.Source.UH H V₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (B : Subgroup (H ⧸ pCore 2 H)) (hB : IsMinimalBestOffender σ B)
    (hBA : B ≤ ((conjugate (Section08.Source.VH H V) (g : G) ⊓
      (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))
    (K : Subgroup H) (hKC : K.IsCComponent) (hK : IsComponent (H ⧸ pCore 2 H)
      (K.map (QuotientGroup.mk' (pCore 2 H))))
    (hk : PlusAction.kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) = H.pCoreIn 2)
    (hcomm : ⁅K.map (QuotientGroup.mk' (pCore 2 H)),B⁆ = K.map (QuotientGroup.mk' (pCore 2 H)))
    (hcentral : K.map H.subtype ≤ centralizer (PlusAction.fixedLayer
      (ConjugateIntersections.sourceSetup T L V V₃ V₁ H) : Set G)) :
    let U := Section08.Source.UH H V₃
    let Q := (L ⊔ (T : Subgroup G) : Subgroup G).pCoreIn 2
    let A := conjugate (Section08.Source.VH H V) (g : G) ⊓ Q
    let Ug := conjugate U (g : G)
    let π := QuotientGroup.mk' (pCore 2 H)
    ∃ hE : IsElementaryAbelian 2 U, letI := hE;
      ∃ (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (U ⧸ V₁.subgroupOf U)))
        (c : BinaryConjugationSection H U V₁ (ρ.comp π)),
        Function.Injective ρ ∧
        (∀ u : U, (c.coordinates u).toAdd = Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf U) u)) ∧
        IsOffender ρ ((A.subgroupOf H).map π) ∧
        IsOffender ρ ((Ug.subgroupOf H).map π) ∧
        IsIrrPlus ρ (K.map π) (subspaceCommutator ρ ⊤ (K.map π)) := by
  obtain ⟨hE,ρ,c,hf,hcoord,hA,hUg⟩ := source_tilde_offenders d h hU hV g hs hout
  let := hE
  exact ⟨hE,ρ,c,hf,hcoord,hA,hUg,source_tilde_component_irrPlus d h hU hV hne g hs hout
    σ s B hB hBA K hKC hK hk hcomm ρ c hcentral⟩

end CFSG.Quasithin.Chapter13.Section07

