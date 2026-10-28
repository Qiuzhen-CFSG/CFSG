module

public import Theory.GroupAction.SylowPointwiseInner.Intrinsic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.CentralQuotient.Models
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.Normalizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.BinaryLinear.SylowPointwiseInner
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# The three ambient natural actions in original 13.5.21

For the alternating-eight and derived binary G₂ components, the remaining
generator fixes an intrinsic Sylow pointwise. The proved automorphism
fixer theorems make it inner, and the trivial component centralizer places
it inside the component. Thus the ambient group equals that component.
For alternating six the faithful natural normalizer instead supplies the
proper symmetric-six extension, retaining the original alternating marking.

These are the actual NaturalAction endpoints consumed by the chief-module
assembly; neither an ambient group identification nor an extended module
marking is assumed. Source: Aschbacher--Smith 13.5.21, printed pp.923--924.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.NaturalEndpoints
open ChapterB.QuasisimpleSource
open MarkedModule.CentralQuotient
variable {E W : Type*} [Group E] [Finite E] [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual alternating-eight component has no outer pointwise Sylow fixer. -/
theorem alternating_eight_fixing_sylow_inner
    (P : Sylow 2 (alternatingGroup (Fin 8))) (a : MulAut (alternatingGroup (Fin 8)))
    (ha : ∀ x ∈ P, a x = x) : ∃ z ∈ P, a = MulAut.conj z := by
  let e := Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
    (Atlas.Order20160A8.sl4TwoEquivPSL.symm.trans (BinaryLinear.OuterCyclic.slEquivLinear 4))
  exact MulAut.fixing_sylow_inner_of_equiv e
    (BinaryLinear.OuterCyclic.sylow_fixing_inner (Or.inl rfl)) P a ha

/-- The original Sylow-central generator leaves the alternating-eight natural
component unchanged, with its literal module coordinates. -/
theorem alternating_eight (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [L.Normal] (hfaith : centralizer (L : Set E) = ⊥)
    (a : ActionEquiv (ρ.comp L.subtype) (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)))
    (P : Sylow 2 L) (t : E)
    (hc : ∀ x ∈ P, (x : E) * t = t * (x : E))
    (hgen : L ⊔ zpowers t = ⊤) : NaturalAction L ρ := by
  have hL := normal_eq_top_of_intrinsic_sylow_generator L hfaith a.groupEquiv
    alternating_eight_fixing_sylow_inner P t hc hgen
  subst L
  exact Or.inr (Or.inl ⟨topEquiv.symm.trans a.groupEquiv, a.linearEquiv, rfl,
    fun g w => a.intertwines ⟨g, mem_top g⟩ w⟩)

/-- The same intrinsic argument for the derived binary G₂ natural action. -/
theorem g2_two (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [L.Normal] (hfaith : centralizer (L : Set E) = ⊥)
    (a : ActionEquiv (ρ.comp L.subtype) (g2DerivedNatural (ZMod 2)))
    (P : Sylow 2 L) (t : E)
    (hc : ∀ x ∈ P, (x : E) * t = t * (x : E))
    (hgen : L ⊔ zpowers t = ⊤) : NaturalAction L ρ := by
  have hL := normal_eq_top_of_intrinsic_sylow_generator L hfaith a.groupEquiv
    (Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
      Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective) P t hc hgen
  subst L
  exact Or.inr (Or.inr ⟨topEquiv.symm.trans a.groupEquiv, a.linearEquiv, rfl,
    fun g w => a.intertwines ⟨g, mem_top g⟩ w⟩)

omit [Finite E] in
/-- The proper natural alternating-six extension is the marked symmetric-six
natural module, using the concrete polar coordinates of the source. -/
theorem alternating_six (ρ : Representation (ZMod 2) E W)
    (L : Subgroup E) [L.Normal] (hf : Function.Injective ρ) (hproper : L ≠ ⊤)
    (a : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6)) : NaturalAction L ρ := by
  obtain ⟨b⟩ := (ChapterK.Alternating.six_extension_of_normalizer ρ L
    ChapterK.Alternating.RecognitionInputs.Six.normalizer hf a).resolve_left hproper
  let e := topEquiv.symm.trans b.action.groupEquiv
  let f := b.action.linearEquiv.trans
    Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv
  refine Or.inl ⟨e, f, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      have he : e l = (b.subgroupEquiv ⟨l, hl⟩).val := b.compatible ⟨l, hl⟩
      change e l ∈ Theory.SpecificGroups.SymmetricSix.A6
      rw [he]
      exact (b.subgroupEquiv ⟨l, hl⟩).property
    · intro hx
      let l := b.subgroupEquiv.symm ⟨x, hx⟩
      refine ⟨l.val, l.property, ?_⟩
      have he : e l.val = (b.subgroupEquiv l).val := b.compatible l
      exact he.trans (congrArg Subtype.val (b.subgroupEquiv.apply_symm_apply ⟨x, hx⟩))
  · intro g w
    change Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv
      (b.action.linearEquiv (ρ g w)) = _
    have hi : b.action.linearEquiv (ρ g w) =
        BinaryPermutation.naturalRepresentation (Fin 6) (e g) (b.action.linearEquiv w) :=
      b.action.intertwines ⟨g, mem_top g⟩ w
    rw [hi]
    exact (Theory.SpecificGroups.SymmetricSix.BinaryNaturalComparison.naturalLinearEquiv_equivariant
      (e g) (b.action.linearEquiv w)).trans
      (Theory.SpecificGroups.SymmetricSix.polarRepresentation_apply (e g) (f w))

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.NaturalEndpoints
