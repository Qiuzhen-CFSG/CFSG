module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeThreeFree
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeImage
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuShadowRows.ThreeFreeSieve
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection

/-!
# Excluding the original M24 code

The original H-star parabolic is nonsolvable and has order prime to
three. The same code pair gives an order-two image of the original V in
H/O₂(H). Its nonzero four-space is H-invariant, so the original TI
property makes the actual maximal subgroup normalize V. The three-free
component sieve now contradicts the surviving order-two image. Existence
of H-star follows from the unchanged many-overgroups hypotheses.

The full automizer marking consequently selects cocode when the original
component quotient is M24. This does not yet exclude the remaining M22
code row. No ambient J4 recognition or no-J4 hypothesis is used here.
The private import reuses only the existing generic intrinsic-source
transport, preserving its public boundary.

Source: Aschbacher--Smith 8.2.9(3), printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode Atlas.Codes
open MathieuCode.SextetLayers.CoordinateTransport
open Chapter7.NormalizedSource.MathieuShadowRows
open Chapter8.Section02.HermitianSource Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual code parabolic contradicts the three-free component sieve. -/
theorem sourceOrbit_m24_code_parabolic_impossible
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    False := by
  obtain ⟨h28,_⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,_,hout⟩ := intrinsic_source_data h28 R hR hP hM
  obtain ⟨I,i,S,s,hu,hHU,hcore,hinter,hcard⟩ :=
    D.sourceOrbit_m24_code_parabolic_image_two h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  have hUn : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hMV : H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hHU)).trans
      (inf_normalizer_le_of_trivial_intersections
        (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti hUn
        (show U ≤ D.sourceOrbit from inf_le_left))
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact hMV ⟨x.property,hx⟩
  exact source_three_free_image_two_impossible h28.sqtk R hP
    (D.sourceOrbit_m24_code_parabolic_not_solvable h hmany hV hq hnon a E hE hH)
    (D.sourceOrbit_m24_code_parabolic_three_free h hmany hV hq hnon a E hE hH)
    (D.sourceOrbit.subgroupOf H) hVR hout hmax hcard.le

/-- Source 8.2.9(3): the original full automizer cannot act as M24 code. -/
theorem sourceOrbit_not_m24_code_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v)) :
    False := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have h127 := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have hu := F.lemma_3_2_3_uniqueness h127
  obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside
    (Chapter3.hasMaximalOutside_of_many T hmany F.maximalLocal hu.1
      ((show (T : Subgroup G) ≤ Chapter3.Section02.localJoin T L from le_sup_right).trans hu.2.1))
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    simpa only [Chapter3.Section02.FundamentalSetup.maximalLocal,D.localOrbit_eq] using hH
  exact D.sourceOrbit_m24_code_parabolic_impossible h hmany hV hq hnon a E hE hH'

/-- Once the original quotient is M24, its full automizer carries the
actual cocode on the unchanged original orbit. -/
theorem sourceOrbit_m24_cocode_marking_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M24,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          cocodeRepresentation (a b) (E v) := by
  obtain ⟨a,he | he⟩ := D.sourceOrbit_m24_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq
  · obtain ⟨E⟩ := he
    exact ⟨a,E.toLinearEquiv,fun b v => LinearMap.congr_fun (E.isIntertwining' b) v⟩
  · obtain ⟨E⟩ := he
    exact (D.sourceOrbit_not_m24_code_of_many h hmany hV hq hnon a E.toLinearEquiv
      (fun b v => LinearMap.congr_fun (E.isIntertwining' b) v)).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
