module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked

/-!
# The original marked first summand in the source reduction

OriginalData constructs the action on the literal fixed image of tau in U/E,
the paired surjection with kernel E, its exact centralizer-action kernel, and
the actual temporary quotient product. These discharge the corresponding
fields of TemporarySource; the full-core theorem then supplies same-I best
generation and the field reduction applies to this very action.

The local transvection geometry, maximum-family/Sylow comparisons and marker
identities remain explicit preceding line-source facts. The universal earlier
classifier and precise unreduced central-quotient/Borel witness remain explicit
as authorized for this conditional prerequisite. The final original-I0 and
index-three conclusions belong to Offenders.

All quotient-module instances are those constructed by OriginalData; keeping
these identical avoids expensive comparisons of independently synthesized
conjugation and quotient-module structures.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154; B.1.2–3, p.68;
B.4.2 and B.5.1, pp.86 and 99.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly
open FullCoreTransfer Replacement.Transvections ChapterB.SourceInduction
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {K : GroupClass.{u}} {Y T V M E Pc : Subgroup G} [IsMulCommutative V]

section Original
variable (o : Replacement.Geometry.OriginalData Y T V M E Pc)
  (dt : TemporaryData Y T V E)
  (hG : IsSQTK K (temporaryLineNormalizer T V E))
  (Z : Subgroup G) (hZV : Z ≤ V)
  (hZ : Nat.Coprime 3 (Nat.card (normalizer (Z : Set G))))
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))
  (geom : letI := o.module_normal
    letI := o.module_elementary
    FixedGeometry (localRepresentation T V E f hf hker)
    (f dt.tau) (f dt.conjugator) (localLineSpace T V E))
  (hmax : ∃ B ∈ Stellmacher.elementaryAbelianMaxSubgroups
    ((lineT T E).subgroupOf (temporaryLineNormalizer T V E)), B ≤ localCentralizer T V E)
  (hcompare : ∀ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (centralizerSylow T V E),
    A ∈ Stellmacher.elementaryAbelianMaxSubgroups (localCentralizer T V E))
  (S : Sylow 2 ((localCentralizer T V E).map (QuotientGroup.mk' (localCore T V E))))
  (hS : (S : Subgroup _).map ((localCentralizer T V E).map
    (QuotientGroup.mk' (localCore T V E))).subtype =
      (centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E)))
  (hI : thompsonImage T V E ≠ ⊥)

local notation "σ₀" => o.pairedRepresentation f hf hker
local notation "ρ₀" => MonoidHom.comp (o.pairedRepresentation f hf hker)
  (Subgroup.subtype (thompsonImage T V E))
local notation "W₀" => Replacement.MarkedSection.fixedImage
  (Replacement.Transvections.localSpan T V E) (localLine T V E) o.tau

/-- OriginalData discharges the actual paired quotient, its first-summand
kernel and the S3 times centralizer-factor product. -/
noncomputable def originalSource :
    letI := o.module_normal
    letI := o.module_elementary
    ∀ (P : Submodule (ZMod 2) W₀), P ≠ ⊥ →
    P ≤ fixedSpace σ₀
      ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))) →
    Submodule.span (ZMod 2)
      {w | ∃ (g : thompsonImage T V E) (v : W₀), v ∈ P ∧ σ₀ g v = w} = ⊤ →
    (∀ x ∈ localCentralizer T V E,
      QuotientGroup.mk' (localCore T V E) x ∈ thompsonImage T V E →
      (∀ w ∈ P, σ₀ (QuotientGroup.mk' (localCore T V E) x) w = w) →
        ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E) →
    (∀ g ∈ normalizer (markedThompson T V E : Set (thompsonImage T V E)),
      ∀ v ∈ P, σ₀ g v = v) →
    TemporarySource (W := W₀) K Y T V E L σ₀ := by
  letI := o.module_normal
  letI := o.module_elementary
  dsimp only
  intro P hP hfix hspan hmarker hnormalizer
  exact {
    temporary := dt
    sqtk := hG
    Z := Z
    Z_le := hZV
    Z_normalizer := hZ
    action := f
    surjective := hf
    kernel := hker
    geometry := geom
    paired := o.pairedSection f hf hker
    paired_kernel := o.pairedRepresentation_centralizer_ker f hf hker
    maximum_exists := hmax
    maximum_comparison := hcompare
    product := o.markedQuotientFactors.equiv
    sylow := S
    sylow_image := hS
    actor_nontrivial := hI
    marker := P
    marker_nonzero := hP
    marker_fixed := hfix
    marker_span := hspan
    marker_centralizer := hmarker
    normalizer_fixed := hnormalizer
 }

include dt hG hZV hZ geom hmax hcompare hS hI in
/-- Apply full-core generation and field reduction on OriginalData's actual
marked first summand. All preceding source and earlier classification inputs
remain explicit; no generation or splitting assumption is added. -/
theorem original_reduce_fields (classify : AdequateClassificationInput.{u,u} K) :
    let := o.module_normal
    let := o.module_elementary
    ∀ (P : Submodule (ZMod 2) W₀), P ≠ ⊥ →
    P ≤ fixedSpace σ₀
      ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E))) →
    Submodule.span (ZMod 2)
      {w | ∃ (g : thompsonImage T V E) (v : W₀), v ∈ P ∧ σ₀ g v = w} = ⊤ →
    (∀ x ∈ localCentralizer T V E,
      QuotientGroup.mk' (localCore T V E) x ∈ thompsonImage T V E →
      (∀ w ∈ P, σ₀ (QuotientGroup.mk' (localCore T V E) x) w = w) →
        ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E) →
    (∀ g ∈ normalizer (markedThompson T V E : Set (thompsonImage T V E)),
      ∀ v ∈ P, σ₀ g v = v) →
    ∀ a : UnreducedAlternative (imageRepresentation ρ₀)
      (TemporarySource.imageThompson (σ := σ₀) (T := T) (V := V) (E := E)),
    offenderSubgroup ρ₀ = ⊤ ∧
    FFHypothesis K (imageRepresentation ρ₀) ∧
    NontrivialAdequateAlternative (imageRepresentation ρ₀) ∧
    RankOneModel (imageRepresentation ρ₀) ∧
    a.fieldDegree = 1 ∧
    (Nonempty (actionImage ρ₀ ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (actionImage ρ₀ ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (actionImage ρ₀ ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) := by
  let := o.module_normal
  let := o.module_elementary
  dsimp only
  intro P hP hfix hspan hmarker hnormalizer a
  let d := originalSource o dt hG Z hZV hZ f hf hker geom hmax hcompare S hS hI P hP
    hfix hspan hmarker hnormalizer
  exact d.reduce_fields classify a
end Original
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.SourceAssembly
