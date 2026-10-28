module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Source
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.SourceAssembly.Transport

/-!
# Source-specialized best generation and field reduction

The full-core theorem proves best generation on the literal temporary
I = q(J(C_H(E))). Its action kernel remains explicit and odd. The source
normalizer bound at Z makes the kernel prime to three, so the product quotient
and SQTK bound give three-rank one in the faithful first-summand image.
Odd-kernel transport supplies best generation there as well; faithfulness,
trivial two-core and the genuine SQTK cover then instantiate the full earlier
B.5.6 classifier. Its quasisimple branch retains every B.5.1 clause, and the
separate B.5.1 application retains the genuine component hypotheses.

The maximum-family comparison places the literal q(J(S_E)) in I. The compatible
Sylow is I intersect q(S_E), and its action image and original marker are kept
through the normalizer transport. `reduce_fields` applies the checked Borel
fixed-space argument to the precise preceding central-quotient/Borel witness:
it starts with arbitrary positive SL2 degree and positive odd SL3 degree,
retains one or two natural copies and a possibly nonsplit central fixed kernel,
and proves degree one. The full classifier also retains central sections with
trivial outer quotients, without asserting that those extensions split.

This is the conditional prerequisite for Offenders. Its source assembly must
supply the preceding local geometry, marker identities, maximum/Sylow data,
the universal earlier classifier, and the exact central-quotient/Borel witness.
There is no all-maximum-images-best or DoubledCentralLift premise. The original
I0 identification and index-three calculation are not conclusions here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.1.2–3, printed p.68; B.4.2, p.86; B.5.1 and B.5.6, pp.99–105;
proof of 15.3.67, pp.1153–1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly
open FullCoreTransfer Replacement.Transvections ChapterB.SourceInduction
universe u
variable {G L W : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The source S_E = C_T(E), inside the temporary normalizer. -/
abbrev centralizerSylow (T V E : Subgroup G) :=
  (T ⊓ centralizer (E : Set G)).subgroupOf (temporaryLineNormalizer T V E)

/-- The literal image of J(S_E), restricted to the same temporary actor I. -/
noncomputable abbrev markedThompson (T V E : Subgroup G) :=
  ((Stellmacher.elementaryAbelianMaxJ (centralizerSylow T V E)).map
    (QuotientGroup.mk' (localCore T V E))).subgroupOf (thompsonImage T V E)

variable {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W}

/-- Preceding line-source data. Every map has its literal source domain. There
is no bestness, generation, field restriction, or splitting assumption. -/
structure TemporarySource (K : GroupClass.{u}) (Y T V E : Subgroup G) [IsMulCommutative V]
    [(Replacement.Transvections.localSpan T V E).Normal]
    [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
    (L : Type u) [Group L]
    (σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) W) where
  temporary : TemporaryData Y T V E
  sqtk : IsSQTK K (temporaryLineNormalizer T V E)
  Z : Subgroup G
  Z_le : Z ≤ V
  Z_normalizer : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G)))
  action : temporaryLineNormalizer T V E →* L
  surjective : Function.Surjective action
  kernel : action.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E))
  geometry : FixedGeometry (localRepresentation T V E action surjective kernel)
    (action temporary.tau) (action temporary.conjugator) (localLineSpace T V E)
  paired : PairedSection (Replacement.Transvections.localSpan T V E) (localLine T V E)
    (localCentralizer T V E) (localCore T V E) action surjective kernel σ
  paired_kernel : (σ.comp ((QuotientGroup.mk' (localCore T V E)).comp
      (localCentralizer T V E).subtype)).ker =
    ((Descent.sectionKernel V E).subgroupOf (temporaryLineNormalizer T V E)).subgroupOf
      (localCentralizer T V E)
  maximum_exists : ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups
    ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)), B ≤ localCentralizer T V E
  maximum_comparison : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (centralizerSylow T V E),
    A ∈ Stellmacher.elementaryAbelianMaxSubgroups (localCentralizer T V E)
  product : ((temporaryLineNormalizer T V E) ⧸ localCore T V E) ≃*
    (Equiv.Perm (Fin 3) × (localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E)))
  sylow : Sylow 2 ((localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E)))
  sylow_image : (sylow : Subgroup _).map ((localCentralizer T V E).map
    (QuotientGroup.mk' (localCore T V E))).subtype =
      (centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))
  actor_nontrivial : thompsonImage T V E ≠ ⊥
  marker : Submodule (ZMod 2) W
  marker_nonzero : marker ≠ ⊥
  marker_fixed : marker ≤ fixedSpace σ
    ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E)))
  marker_span : Submodule.span (ZMod 2)
    {w | ∃ (g : thompsonImage T V E) (v : W), v ∈ marker ∧ σ g v = w} = ⊤
  marker_centralizer : ∀ x ∈ localCentralizer T V E,
    QuotientGroup.mk' (localCore T V E) x ∈ thompsonImage T V E →
    (∀ w ∈ marker, σ (QuotientGroup.mk' (localCore T V E) x) w = w) →
      ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E
  normalizer_fixed : ∀ g ∈ normalizer (markedThompson T V E : Set (thompsonImage T V E)),
    ∀ v ∈ marker, σ g v = v

namespace TemporarySource
variable (d : TemporarySource K Y T V E L σ)

omit [Finite G] [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)] in
private theorem sylow_le_lineT :
    (centralizerSylow T V E) ≤ (lineT T E).subgroupOf (temporaryLineNormalizer T V E) := by
  intro x hx
  exact ⟨hx.1, centralizer_le_normalizer (E : Set G) hx.2⟩

include d

omit [Finite G] in
private theorem sylow_isPGroup : IsPGroup 2 (centralizerSylow T V E) := by
  have hT : IsPGroup 2 (lineT T E) := by
    rw [← d.temporary.sylow_eq]
    exact d.temporary.sylow.isPGroup'.map _
  exact hT.comap_subtype.to_le (sylow_le_lineT (T := T) (V := V) (E := E))

omit [Finite G] in
private theorem sylow_image_le :
    (d.sylow : Subgroup _).map ((localCentralizer T V E).map
      (QuotientGroup.mk' (localCore T V E))).subtype ≤
        ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)).map
          (QuotientGroup.mk' (localCore T V E)) := by
  rw [d.sylow_image]
  exact map_mono sylow_le_lineT

variable [FiniteDimensional (ZMod 2) W]

/-- Full-core transfer establishes generation on the original I itself. -/
theorem generated (classify : AdequateClassificationInput.{u,u} K) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ := by
  apply temporary_thompson_image_generated classify Y T V E d.Z d.temporary d.sqtk
    d.Z_le d.Z_normalizer d.action d.surjective d.kernel d.geometry σ d.paired
    d.paired_kernel d.maximum_exists d.product d.sylow (by exact sylow_image_le d) d.marker
  · rw [d.sylow_image]
    exact d.marker_fixed
  · exact d.marker_span
  · exact d.marker_centralizer

omit [FiniteDimensional (ZMod 2) W] in
/-- The same actor retains its actual odd action kernel. -/
theorem odd_kernel : Odd (Nat.card (actionHom (σ.comp (thompsonImage T V E).subtype)).ker) := by
  obtain ⟨_, _, hodd⟩ := temporary_compatible_sylow_and_odd_kernel Y T V E d.temporary σ
    d.paired_kernel d.sylow (by exact sylow_image_le d)
  exact hodd

omit [FiniteDimensional (ZMod 2) W] in
/-- Three-rank one follows from the actual product quotient and SQTK cover. -/
theorem threeRank : primeRank 3 (thompsonImage T V E) ≤ 1 := by
  have hQ : IsPGroup 2 (localCore T V E) := by
    rw [localCore_eq_pCore]
    exact pCore_isPGroup
  exact thompsonImage_threeRank_le_one (localCore T V E) (localCentralizer T V E)
    (Stellmacher.elementaryAbelianMaxJ (localCentralizer T V E)) hQ
    (d.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (sSup_le fun _ hA => hA.1) d.product

/-- The marker uses the compatible Sylow intersection and the literal image
of J(S_E); the maximum-family comparison supplies its containment. -/
noncomputable def marked : MarkedNormalizer
    (σ.comp (thompsonImage T V E).subtype) (markedThompson T V E) := by
  let hs := temporary_compatible_sylow_and_odd_kernel Y T V E d.temporary σ
    d.paired_kernel d.sylow (by exact sylow_image_le d)
  let S := hs.choose
  have hS := hs.choose_spec.1
  have hJ := (sylow_contains_marked_thompson_image
    (localCentralizer T V E) (centralizerSylow T V E) (localCore T V E)
    (by exact sylow_isPGroup d) d.maximum_comparison).2.1
  refine ⟨S, ?_, d.marker, d.marker_nonzero, ?_, d.marker_span, d.normalizer_fixed⟩
  · rw [hS, d.sylow_image]
    exact hJ
  · intro v hv s
    have hs := hS.le s.property
    rw [d.sylow_image] at hs
    exact d.marker_fixed hv ⟨s.val, hs⟩

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- Mapping back to H/Q recovers exactly q(J(S_E)), so subgroupOf has
not silently replaced the marked subgroup by a proper intersection. -/
theorem markedThompson_map :
    (markedThompson T V E).map (thompsonImage T V E).subtype =
      (Stellmacher.elementaryAbelianMaxJ (centralizerSylow T V E)).map
        (QuotientGroup.mk' (localCore T V E)) := by
  exact map_subgroupOf_eq_of_le (sylow_contains_marked_thompson_image
    (localCentralizer T V E) (centralizerSylow T V E) (localCore T V E)
    (by exact sylow_isPGroup d) d.maximum_comparison).1

omit [FiniteDimensional (ZMod 2) W] in
/-- The selected Sylow is the compatible intersection with q(S_E). -/
theorem marked_sylow_eq : (d.marked.sylow : Subgroup (thompsonImage T V E)) =
    ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))).subgroupOf
      (thompsonImage T V E) := by
  exact (temporary_compatible_sylow_and_odd_kernel Y T V E d.temporary σ
    d.paired_kernel d.sylow (by exact sylow_image_le d)).choose_spec.1.trans
      (congrArg (fun A => A.subgroupOf (thompsonImage T V E)) d.sylow_image)

/-- The subgroup used by every model calculation is exactly pi(q(J(S_E))). -/
noncomputable abbrev imageThompson :=
  actionSubgroup (σ.comp (thompsonImage T V E).subtype) (markedThompson T V E)

/-- Descend the same marker and its normalizer along the actual odd kernel. -/
noncomputable def imageMarked : MarkedNormalizer
    (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
    (imageThompson (σ := σ) (T := T) (V := V) (E := E)) :=
  marked_actionImage d.marked d.odd_kernel

omit [FiniteDimensional (ZMod 2) W] in
/-- The faithful-image marker is the original specified subspace. -/
@[simp] theorem imageMarked_marker : d.imageMarked.marker = d.marker := rfl

omit [FiniteDimensional (ZMod 2) W] in
/-- The faithful-image Sylow retains the literal compatible intersection. -/
theorem imageMarked_sylow : (d.imageMarked.sylow : Subgroup _) =
    actionSubgroup (σ.comp (thompsonImage T V E).subtype)
      (((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))).subgroupOf
        (thompsonImage T V E)) := by
  change (d.marked.sylow : Subgroup (thompsonImage T V E)).map
    (actionHom (σ.comp (thompsonImage T V E).subtype)) = _
  rw [d.marked_sylow_eq]
  rfl

/-- B.5.3's full hypotheses on the whole faithful image, not on a proper
best-generated subgroup. The original I remains separately best-generated. -/
theorem imageHypothesis (classify : AdequateClassificationInput.{u,u} K) :
    FFHypothesis K (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) := by
  let ρ := σ.comp (thompsonImage T V E).subtype
  exact ⟨inferInstance, imageRepresentation_injective ρ,
    actionImage_twoCore_eq_bot_of_sylow_fixed_span ρ d.marked.sylow d.marked.marker
      d.marked.sylow_fixes d.marked.orbit_span,
    generated_actionImage ρ d.odd_kernel (d.generated classify),
    ⟨actionImage_sqtkCover d.sqtk (QuotientGroup.mk' (localCore T V E))
      (QuotientGroup.mk'_surjective _) (thompsonImage T V E) σ⟩⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- The actual prime-to-three kernel is needed for rank transport. Oddness
alone would not justify this comparison. -/
theorem image_threeRank : primeRank 3
    (actionImage (σ.comp (thompsonImage T V E).subtype)) ≤ 1 := by
  have hEU : localLine T V E ≤ Replacement.Transvections.localSpan T V E :=
    comap_mono (d.temporary.line_le.trans (le_conjugateSpanBy V (lineNormalizer E)))
  let : IsElementaryAbelian 2 (localLine T V E) := IsElementaryAbelian.of_le hEU
  have hP := temporary_markerCentralizer_coprime_three Y T V E d.Z d.temporary
    d.Z_le d.Z_normalizer σ d.marker d.marker_centralizer
  exact (primeRank_le_of_surjective_of_coprime 3
    (actionHom (σ.comp (thompsonImage T V E).subtype))
    (MonoidHom.rangeRestrict_surjective _)
    (action_kernel_coprime_three_of_marker _ d.marker hP)).trans d.threeRank

/-- The same-image full B.5.6 alternative retains all B.5.1 clauses in its
quasisimple branch. Generation is supplied by the full-core theorem above. -/
theorem classification (classify : AdequateClassificationInput.{u,u} K) :
    NontrivialAdequateAlternative (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) := by
  let ρ := σ.comp (thompsonImage T V E).subtype
  let : Nontrivial (thompsonImage T V E) := (Subgroup.nontrivial_iff_ne_bot _).mpr d.actor_nontrivial
  obtain ⟨A, hA⟩ := ff_of_generated ρ (d.generated classify)
  have hff : IsFFModule (imageRepresentation ρ) := ⟨_, hA.actionImage_of_odd_kernel ρ d.odd_kernel⟩
  exact (classify _ W (imageRepresentation ρ) (d.imageHypothesis classify)).of_ff _ hff

/-- Unreduced natural SL2, odd-degree SL3 (one or two copies), or S5,
with their actual embedded module sections and both nonsplit orientations. -/
theorem unreduced_models (classify : AdequateClassificationInput.{u,u} K) :
    RankOneModel (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) :=
  RankOneDispatch.model_of_adequate_alternative _ (d.imageHypothesis classify)
    d.image_threeRank (d.classification classify)

/-- Direct B.5.1 application when its genuine component hypotheses are
available. No F-star, quasisimplicity or faithfulness premise is inferred
from an ordinary offender. The generation field is discharged by full-core
transfer and odd-kernel transport. -/
theorem quasisimple_classification (classify : AdequateClassificationInput.{u,u} K)
    (b51 : ProjectiveLine.QuasisimpleClassificationInput.{u,u} K)
    (F : Subgroup (actionImage (σ.comp (thompsonImage T V E).subtype)))
    (hF : Theory.GroupTheory.IsQuasisimple F) (hFK : IsSQTK K F)
    (hfit : Theory.GroupTheory.generalizedFitting
      (actionImage (σ.comp (thompsonImage T V E).subtype)) = F ⊔ center _) :
    Nonempty (ProjectiveLine.QuasisimpleSourceConclusion
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) F) := by
  have h := d.imageHypothesis classify
  exact b51 _ W _ F ⟨h.finite_module, h.faithful, hF, hFK, hfit, h.twoCore, h.generated⟩

/-- Final conditional field reduction on the actual faithful image. The
precise preceding central-quotient/Borel witness is explicit: its fields
start at arbitrary positive degree, and its J is the literal pi(q(J(S_E))).
The original actor's generation, full classifier output, module sections and
central quotient witness all refer to this same action and survive assembly. -/
theorem reduce_fields (classify : AdequateClassificationInput.{u,u} K)
    (a : UnreducedAlternative (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (imageThompson (σ := σ) (T := T) (V := V) (E := E))) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    FFHypothesis K (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) ∧
    NontrivialAdequateAlternative (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) ∧
    RankOneModel (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) ∧
    a.fieldDegree = 1 ∧
    (Nonempty (actionImage (σ.comp (thompsonImage T V E).subtype) ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (actionImage (σ.comp (thompsonImage T V E).subtype) ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (actionImage (σ.comp (thompsonImage T V E).subtype) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) :=
  ⟨d.generated classify, d.imageHypothesis classify, d.classification classify,
    d.unreduced_models classify, a.field_degree_eq_one d.imageMarked, a.small_group_cases d.imageMarked⟩
end TemporarySource
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly
