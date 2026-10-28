module

public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.NativeBounds
public import Theory.Representation.Mathieu.M24SmallFF
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.M24Spectrum
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.Large.GM02.M24Displacement
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Remaining
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.OddClasses
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.Consumer
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.BinaryModels
public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.ExteriorBound

/-!
# The quadratic exclusion for small native M24 modules

A simple constituent of the M23 restriction supplies a nonzero map from the
permutation module or its tensor product with the code or cocode. The native
Golay filtration, exterior contraction and trace-kernel calculations kill all
three maps. Strict quadratic bounds replace the FF hypothesis in the two
simple degree-eleven factors; no module recognition is assumed.

The complete native large-model construction supplies the degree-eleven
conclusion for the original source action. This discharges the remaining
premise in the unmarked exclusion, preserving the central quotient and
the whole ambient action.

Source: Aschbacher--Smith B.4.5 and K.4, printed pp.87 and 457--459.
-/

public section
open Representation Sporadic.Mathieu MathieuCode Representation.BinaryOffender
open Representation.Mathieu.M24SmallFF
open Representation.MathieuM24Degree44.FiveSpace
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M24
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M24 V) [ρ.IsIrreducible]
  (hf : Function.Injective ρ) (hq : quadraticRatio ρ ≤ 2)
  (hd : Module.finrank (ZMod 2) V ≤ 24)

omit [FiniteDimensional (ZMod 2) V] in
include hq in
private lemma code_map_zero (f : codeRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : codeRepresentation.IsIrreducible := code_isIrreducible
  by_contra hn
  let E := (f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hn)).symm
  have hle := quadraticRatio_le_of_injective_equivariant ρ codeRepresentation
    (MonoidHom.id _) Function.injective_id E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v)
  exact (not_lt_of_ge (hle.trans hq)) QuadraticActors.StrictCode.code_quadraticRatio_gt_two

omit [FiniteDimensional (ZMod 2) V] in
include hq in
private lemma cocode_map_zero (f : cocodeRepresentation.IntertwiningMap ρ) : f = 0 := by
  let : cocodeRepresentation.IsIrreducible := cocode_isIrreducible
  by_contra hn
  let E := (f.ofBijective ((IsIrreducible.bijective_or_eq_zero f).resolve_right hn)).symm
  have hle := quadraticRatio_le_of_injective_equivariant ρ cocodeRepresentation
    (MonoidHom.id _) Function.injective_id E.toLinearEquiv
    (fun g v => LinearMap.congr_fun (E.isIntertwining' g) v)
  exact (not_lt_of_ge (hle.trans hq)) cocode_quadraticRatio_gt_two

include hq hd in
private lemma codeExterior_map_zero (f : codeExterior.IntertwiningMap ρ) : f = 0 := by
  apply map_eq_zero_of_ker contraction contraction_surjective (cocode_map_zero ρ hq) f
  let i : kernelRepresentation.IntertwiningMap codeExterior := ⟨kernel.toSubmodule.subtype, fun _ => rfl⟩
  have hi := kernel44_map_zero ρ hd (f.comp i)
  intro v hv
  exact congrArg (fun e : kernelRepresentation.IntertwiningMap ρ => e ⟨v,hv⟩) hi
include hq hd in
private lemma dualCodeExterior_map_zero (f : codeExterior.dual.IntertwiningMap ρ) : f = 0 := by
  let i : cocodeRepresentation.dual.IntertwiningMap codeExterior.dual :=
    ⟨contraction.toLinearMap.dualMap, by
      intro g
      apply LinearMap.ext
      intro φ
      apply LinearMap.ext
      intro v
      exact congrArg φ (LinearMap.congr_fun (contraction.isIntertwining' g⁻¹) v).symm⟩
  let q : codeExterior.dual.IntertwiningMap dualKernelRepresentation :=
    ⟨kernel.toSubmodule.dualRestrict, fun _ => rfl⟩
  apply map_eq_zero_of_ker q (Subspace.dualRestrict_surjective (W := kernel.toSubmodule))
    (dualKernel44_map_zero ρ hd) f
  intro φ hφ
  have hr : φ ∈ LinearMap.range contraction.toLinearMap.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact hφ
  obtain ⟨ψ, rfl⟩ := hr
  have hh := code_map_zero ρ hq ((f.comp i).comp codeDuality.toIntertwiningMap)
  obtain ⟨u, hu⟩ := codeDuality.toLinearEquiv.surjective ψ
  have hv := congrArg (fun e : codeRepresentation.IntertwiningMap ρ => e u) hh
  change f (i (codeDuality u)) = 0 at hv
  change codeDuality u = ψ at hu
  rw [hu] at hv
  exact hv
include hq hd in
private lemma cocodeExterior_map_zero (f : cocodeExterior.IntertwiningMap ρ) : f = 0 := by
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [Subspace.dual_finrank_eq, finrank_cocodeExterior, finrank_codeExterior])).mpr
      exteriorPairingLinear_surjective
  let e := exteriorPairing.ofBijective ⟨hinj, exteriorPairingLinear_surjective⟩
  have hh := dualCodeExterior_map_zero ρ hq hd (f.comp e.symm.toIntertwiningMap)
  ext v
  have he := congrArg (fun q : codeExterior.dual.IntertwiningMap ρ => q (e v)) hh
  change f (e.symm (e v)) = 0 at he
  rw [e.symm_apply_apply] at he
  exact he


include hf hq hd in
/-- The native faithful irreducible action cannot have quadratic ratio at most
two in degrees at most twenty-four. -/
theorem no_small_quadratic : False := by
  have hcode := code_map_zero ρ hq
  have hcocode := cocode_map_zero ρ hq
  have hcc := tensorSquare_map_zero _ _ hcode (codeExterior_map_zero ρ hq hd)
  have hdd := tensorSquare_map_zero _ _ hcocode (cocodeExterior_map_zero ρ hq hd)
  apply Representation.MathieuSmall.M24SmallFF.PointInduction.false_of_native_source_maps_eq_zero ρ hd
  · exact full_maps_zero_of_constituents ρ (trivial_map_zero ρ hf) hcode hcocode
  · exact full_tensor_maps_zero_of_constituents ρ codeRepresentation
      (map_zero_of_equiv (Representation.TensorProduct.lid (ZMod 2) codeRepresentation) hcode)
      hcc (cocode_code_map_zero ρ hf hd)
  · exact full_tensor_maps_zero_of_constituents ρ cocodeRepresentation
      (map_zero_of_equiv (Representation.TensorProduct.lid (ZMod 2) cocodeRepresentation) hcocode)
      (code_cocode_map_zero ρ hf hd) hdd

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M24

namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu
open Subgroup Theory.GroupTheory
open ComponentRecognition.KnownFFTypes.Sporadic.LargeMathieu
open Representation.Mathieu.M24DegreeSpectrum
open Representation.MathieuM24Degree44
universe u v

/-- All source degree inputs except the eight large simple models are discharged.
Their independent producer is the intrinsic M24 completeness development. -/
theorem m24_degree_eleven_of_largeModels
    (hlarge : AbsoluteSpectrum.LargeModelsExist.{v}) : M24DegreeEleven.{u,v} :=
  GM02.m24DegreeEleven_of_absolute_calculations GM02.m24InvolutionGeneration
    (absoluteSmallSpectrum_of_models AbsoluteSpectrum.smallModelsExist hlarge
      AbsoluteSpectrum.oddClassBound) degreeElevenTraceField
    (GM02.m24Degree44Displacement_of_fiveFixedSpaceBound
      (fiveFixedSpaceBound_of_binary_section_models FiveSpace.Placement.binarySectionModels
        hlarge AbsoluteSpectrum.oddClassBound FiveSpace.golayExteriorFiveBound))

/-- Native completeness and the displacement calculation force degree eleven
under the original cubic source hypotheses, including central covers. -/
theorem m24_degree_eleven : M24DegreeEleven.{u,v} :=
  m24_degree_eleven_of_largeModels AbsoluteSpectrum.LargeModels.largeModelsExist

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- Conditional source assembly, retaining the actual central cover and the
whole ambient action. Only the independent large-model existence input remains. -/
theorem no_m24_of_largeModels (hlarge : AbsoluteSpectrum.LargeModelsExist.{v})
    (h : ChapterK.RankOne.SourceHypotheses ρ L) (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier)) : False := by
  rcases h.fitting with rfl
  obtain ⟨q⟩ := he
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Mathieu.M24 := q.symm.isSimpleGroup
  have htop := m24_generalizedFitting_eq_top h.quasisimple q
  let σL := ρ.comp (generalizedFitting G).subtype
  let eL := CentralCover.groupEquiv σL
    (h.faithful.comp Subtype.val_injective) h.irreducible q
  let d : generalizedFitting G ≃* G := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  let e : G ≃* Sporadic.Mathieu.M24 := d.symm.trans eL
  let σ : Representation (ZMod 2) Sporadic.Mathieu.M24 V := ρ.comp e.symm.toMonoidHom
  have hiρ : ρ.IsIrreducible :=
    (irreducible_comp_surjective_iff (generalizedFitting G).subtype
      (fun g => ⟨d.symm g,d.apply_symm_apply g⟩) ρ).mp h.irreducible
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective ρ).mpr hiρ
  have hfσ : Function.Injective σ := h.faithful.comp e.symm.injective
  have hqσ : quadraticRatio σ ≤ 2 :=
    (quadraticRatio_le_of_injective_equivariant ρ σ e.toMonoidHom e.injective
      (LinearEquiv.refl _ _) (fun g v => by
        change ρ g v = ρ (e.symm (e g)) v
        rw [e.symm_apply_apply])).trans hq
  have hd := m24_degree_eleven_of_largeModels hlarge ρ
    ⟨h.sqtk, h.quasisimple, h.faithful, h.irreducible, h.smallCubic⟩ ⟨q⟩
  exact M24.no_small_quadratic σ hfσ hqσ (by omega)

/-- Exclude the actual M24 central quotient from the small-quadratic source.
The native model construction discharges the completeness premise. -/
theorem no_m24 (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier)) : False :=
  no_m24_of_largeModels AbsoluteSpectrum.LargeModels.largeModelsExist h hq he

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- The literal B.4 consumer of the conditional M24 exclusion. -/
theorem b4_no_m24_of_largeModels [Finite V]
    (hlarge : AbsoluteSpectrum.LargeModelsExist.{v})
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.m24.Carrier)) : False :=
  no_m24_of_largeModels hlarge ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq he

open Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases in
/-- Exclude the M24 constructor of the remaining-model sieve under the
literal B.4 hypotheses and quadratic bound, with no additional premises. -/
theorem b4_no_m24 [Finite V]
    (h : B4Hypotheses KnownSimple.IsKnownSimple ρ) (hq : quadraticRatio ρ ≤ 2)
    (he : Nonempty (generalizedFitting G ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.m24.Carrier)) : False :=
  no_m24 ⟨h.sqtk, rfl, h.quasisimple, h.faithful, h.irreducible,
    (Representation.BinaryOffender.cubicRatio_le_quadraticRatio ρ).trans hq⟩ hq he

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu
