module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceMarker.Application
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceRanks
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.OriginalComparison.FullAction

/-!
# Original offender conclusions with all local marker premises discharged

SourceMarker constructs the literal projected V/E marker from the preceding
normalizer, Thompson and product statements. Its application supplies all
temporary Sylow, maximum-family, core, paired-action and marker data.
The original-I₀ comparison then gives its S₃ action image, exact kernel and
index-three intersection. Frattini transport on the actual paired quotient
also gives dimension two for the commutator under the full original I.

The universal adequate classifier and the precise unreduced B.4/B.5
central-quotient/Borel witness remain explicit earlier-source obligations.
The former belongs to the general B.5 classification owner. The latter is
stronger than the embedded ModelSection produced by RankOneDispatch: its
whole central quotient and its literal marked Thompson normalizer still need
construction. Thus these conditional conclusions do not complete 15.3.67.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceAssembly
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly OriginalComparison ChapterB.SourceInduction
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {K : GroupClass.{u}} {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G))
  (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
  (hprod : (lineNormalizer E : Set G) = (lineI E : Set G) * (lineM M E : Set G))
  (hNJ : normalizer (elementaryAbelianMaxJ (lineT T E) : Set G) ≤ M)
  (hG : IsSQTK K (lineNormalizer E))
  (Z : Subgroup G) (hZV : Z ≤ V)
  (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))

/-- On the literal first summand and its marked conjugate, the extended
full-I action agrees with conjugation on the actual original U/E. -/
theorem source_projection_conjugate :
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
    let σ := o.pairedRepresentation f hf hker
    let π := (o.pairedSection f hf hker).projection
    let ρ := FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker)
    ∀ (i : lineI E) (v : Additive (Replacement.Transvections.localSpan T V E)),
      π (FullAction.conjugateVector o i v) = (ρ i (π v).1, ρ i (π v).2) := by
  let := o.module_normal
  let := o.module_elementary
  let := Descent.sectionKernel_normal V E o.line_le
  exact FullAction.projection_conjugate o (o.pairedRepresentation f hf hker)
    (o.pairedRepresentation_centralizer_ker f hf hker) f hf hker (o.pairedSection f hf hker)

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- The original-I₀ identification, exact kernel and index, and the full-I
commutator dimension, with marker geometry supplied by its proved producer.
Only the genuine earlier classification witnesses remain beyond the original
local hypotheses. -/
theorem original_conclusions_of_local (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
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
    Module.finrank (ZMod 2) (Coinvariants.ker
      (FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker))) = 2 ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let := o.module_normal
  let := o.module_elementary
  let := Descent.sectionKernel_normal V E o.line_le
  dsimp only
  intro a
  obtain ⟨hgen, hiso, hdim, hkernel, hindex⟩ :=
    original_conclusions o hJ hNM hI hG Z hZV hZ f hf hker
      (SourceMarker.facts o f hf hker hNM hJ hprod hNJ) classify a
  refine ⟨hgen, hiso, hdim, hkernel, ?_, hindex⟩
  rw [FullAction.moved_eq]
  exact hdim

include hJ hNM hI hprod hNJ hG hZV hZ in
/-- Choose the genuine quotient by C_H(U), so the faithful-action map and
its exact kernel are constructed rather than retained as extra premises. The
universal classifier and unreduced marked classification remain explicit. -/
theorem canonical_original_conclusions (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    let := Descent.sectionKernel_normal V E o.line_le
    let C := centralizer
      (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
    let f := QuotientGroup.mk' C
    let hf := QuotientGroup.mk'_surjective C
    let hker := QuotientGroup.ker_mk' C
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
    Module.finrank (ZMod 2) (Coinvariants.ker
      (FullAction.representation o σ (o.pairedRepresentation_centralizer_ker f hf hker))) = 2 ∧
    (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3 := by
  let := o.module_normal
  let := o.module_elementary
  let := Descent.sectionKernel_normal V E o.line_le
  let C := centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
  exact original_conclusions_of_local o hJ hNM hI hprod hNJ hG Z hZV hZ
    (QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C) classify


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceAssembly
