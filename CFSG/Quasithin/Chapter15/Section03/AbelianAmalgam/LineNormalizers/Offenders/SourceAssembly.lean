module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.OriginalComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Identification

/-!
# Conditional original-I₀ assembly with the source marker still outstanding

The original local package constructs the temporary full core, paired action
and transvection geometry. SourceSylow supplies the literal maximum-family,
quotient-Sylow, nontriviality and SQTK transports. Full-core transfer generates
the same I by best offenders. The actual normalizer bound excludes the cubic
alternatives, and the surviving matrix plane identifies the original I₀
action, its exact section kernel, moved dimension and intersection index.

`SourceMarker.Facts` is still a construction obligation from original V and
tau. The universal earlier classifier and the precise unreduced B.4/B.5
central-quotient witness are also explicit earlier-source inputs. Thus this
file does not claim completed 15.3.67; its conclusion is a checked assembly
ready for those producers, without a splitting or all-images-best premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceAssembly
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly OriginalComparison ChapterB.SourceInduction
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {K : GroupClass.{u}} {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
  (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
  (hG : IsSQTK K (lineNormalizer E))
  (Z : Subgroup G) (hZV : Z ≤ V)
  (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
  (marker : SourceMarker.Facts o f hf hker)

/-- Every extra temporary Sylow, maximum, core and geometry input is
discharged from OriginalData and the preceding original Thompson bounds.
Only the explicitly named source marker construction remains as local input. -/
noncomputable def temporarySource :
    let := o.module_normal
    let := o.module_elementary
    TemporarySource K Y T V E L (o.pairedRepresentation f hf hker) := by
  let := o.module_normal
  let := o.module_elementary
  exact originalSource o (temporaryData_of_original o) (SourceSylow.temporary_sqtk hG)
    Z hZV hZ f hf hker (fixedGeometry_of_original o f hf hker)
    (SourceSylow.maximum_exists o hJ) (SourceSylow.maximum_comparison o)
    (SourceSylow.quotient_sylow o).choose (SourceSylow.quotient_sylow o).choose_spec
    (SourceSylow.actor_nontrivial o hJ hNM hI)
    (SourceMarker.projected o f hf hker) marker.nonzero marker.sylow_fixed
    marker.orbit_span (fun x hx _ hfix => marker.displacement x hx hfix) marker.normalizer_fixed

include hJ hNM hI hG hZV hZ marker in
/-- Original I₀ has the S₃ action image, exact section-action kernel and
index-three intersection, conditional on the still-explicit source marker
producer and the genuine unreduced earlier classification. No terminal
conclusion about original G_E is asserted. -/
theorem original_conclusions (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let σ := o.pairedRepresentation f hf hker
    ∀ _a : BestReduction.UnreducedAlternative
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E)),
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (originalRepresentation σ) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2) (Coinvariants.ker (originalRepresentation σ)) = 2 ∧
    (originalRepresentation σ).ker =
      ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
        (originalActor T V E) ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  intro a
  let σ := o.pairedRepresentation f hf hker
  let d := temporarySource o hJ hNM hI hG Z hZV hZ f hf hker marker
  obtain ⟨hgen, ⟨e⟩, hdim, _, hindex⟩ := Identification.temporary_identification d classify a
  have hk := o.pairedRepresentation_centralizer_ker f hf hker
  refine ⟨hgen, ⟨(MulEquiv.subgroupCongr (original_actionImage o σ hk)).trans e⟩,
    ?_, original_kernel σ hk, ?_⟩
  · rw [original_moved_eq o σ hk]
    exact hdim
  · apply original_index o σ hk (SourceMarker.projected o f hf hker) ?_ hindex
    intro x
    exact marker.intersection x.val (originalActor_le_centralizer x.property)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceAssembly
