module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Fitting.Source
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.EndpointKernels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Assembly
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.SourceImage
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial

/-!
# Excluding the actual three-primary branch in 13.8.13

The original ordinary or covered natural flag constructs the cubic residual
generators and the elementary intrinsic quotient of L1. For the selected E9,
its literal conjugation coordinates have an SL2(3) image; the proved character
bound contradicts the quadratic actor. For the selected extraspecial group,
the cubic generators construct an elementary subgroup of order 27, contradicting
strong quasithinness inherited from the original involution centralizer.
Neither a representation model nor a rank witness is assumed.

The final consumer applies the supercritical reduction on the same selected
critical pair and its actual conjugator. Both three-primary alternatives are
excluded, leaving an actual ReducedFive subgroup in the original H. The
preceding source inputs remain precise: F.9 applicability, selected 13.8.8
geometry, 13.3.9, the transvection implication of 13.8.5, the seed commutator,
and the universal D.2.13 prime restriction. No conclusion of the five-primary
exclusion or solvable-overgroup theorem is used.

Source: Aschbacher--Smith, 13.8.13, printed pp.950--951.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SolvableExclusion SolvableExclusion.Three
namespace OddReduction
universe u
variable {G:Type u} [Group G] [Finite G]
 {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H Vα:Subgroup G}
 (d:LocalSetup T L V V₁ V₂ V₃ M G₁)

noncomputable def cubic_generation : Extraspecial.CubicGeneration (one L T V₁) T :=
  Extraspecial.SourceResiduals.of_models (local_flag_alternatives d)
    (fun a=>CoverFactorization.source_factorization a)

include d in
theorem first_quotient_elementary : IsElementaryAbelian 3 (one L T V₁⧸pCore 2 (one L T V₁)) :=
  (cubic_generation d).elementary

include d in
theorem local_stronglyQuasithin (hHG:H≤G₁) : IsStronglyQuasithin H := by
  obtain ⟨z,hz,_,_,_,hG⟩ := LocalFitting.line_involution d
  have hc:H≤centralizer ({z}:Set G) := hHG.trans hG
  exact (d.counterexample.qtke.toIsQTKE.involution_centralizer_stronglyQuasithin hz).of_injective
    (inclusion hc) (inclusion_injective hc)

omit d in
theorem source_kernel
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis) :
    Source.QH H=commutatorPreimage H (Source.UH H V₃) V₁ := by
  have hh:=f9_commutatorPreimage_eq _ hF9 H le_rfl
  exact (hh.trans (inf_eq_right.mpr (map_subtype_le _))).symm

include d in
theorem noncontained_three_impossible
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    {c:CriticalGeometry.CriticalPair L T H V}
    (s:RankOne.Geometry c V₃ V₁ (one L T V₁))
    (r:ReducedOdd 3 H (one L T V₁) T M Vα)
    (hout:¬Source.starImage H (one L T V₁)≤Source.starImage H r.P)
    (hsmall:(IsElementaryAbelian 3 (Source.starImage H r.P) ∧ Nat.card (Source.starImage H r.P)=3^2) ∨
      (IsExtraspecial 3 (Source.starImage H r.P) ∧ Nat.card (Source.starImage H r.P)=3^3 ∧
        ∀x:Source.starImage H r.P,x^3=1))
    (a:Five.StarAction H (Source.UH H V₃) V₁)
    (hQ:CriticalGeometry.Reorientation.QuadraticMember (Supercritical.Offenders.linearAction a)
      (Source.starImage H (c.Ugamma V₃))) : False := by
  have hHG:H≤G₁ := by
    rw [d.first_normalizer]
    exact hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hr:=local_stronglyQuasithin d hHG
  rcases hsmall with ⟨he,hc⟩ | ⟨he,hc,hp⟩
  · let := he
    let := first_quotient_elementary d
    let coordinates := Noncontained.ElementaryNine.source_coordinates r hc
    have hSL := Noncontained.ElementaryNine.source_special_image_of_local_elementary
      d r hc hr hout coordinates
    exact Noncontained.ElementaryNine.false_of_special_image s r coordinates hSL a
      (a.injective_of_kernel (source_kernel hF9)) hQ
  · let := he
    exact Extraspecial.false_of_cubicGeneration r (cubic_generation d) hc hp hout hr

include d in
theorem five_of_selected_source
    (hD213:Supercritical.Offenders.D213PrimeRestriction.{u,u})
    (hF9:(Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    {c:CriticalGeometry.CriticalPair L T H V}
    (s:RankOne.Geometry c V₃ V₁ (one L T V₁))
    (hH:Minimal (·∈Source.Hz (one L T V₁) T G₁ M) H)
    (hs:Group.IsSolvable H)
    (hsource:Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
    (a:Five.StarAction H (Source.UH H V₃) V₁)
    (hQ:CriticalGeometry.Reorientation.QuadraticMember (Supercritical.Offenders.linearAction a)
      (Source.starImage H (c.Ugamma V₃)))
    (h135:Five.TransvectionComponentConclusion a T)
    (hseed:V₃≤⁅V₃,one L T V₁⁆⊔V₁) :
    ∃h:H, c.Vgamma.map (MulAut.conj (h:G)).toMonoidHom≤(one L T V₁⊔(T:Subgroup G)).pCoreIn 2 ∧
      Nonempty (ReducedFive H (one L T V₁) T M
        (c.Vgamma.map (MulAut.conj (h:G)).toMonoidHom)) := by
  obtain ⟨h,hplace⟩:=s.placement
  let : IsElementaryAbelian 2 (conjugateSpanBy V G₁):=d.span_elementary
  let : IsElementaryAbelian 2 (Source.VH H V):=
    IsElementaryAbelian.of_le (conjugateSpanBy_mono le_rfl hH.prop.2.1)
  have hLM:L⊔(T:Subgroup G)≤M := by
    rw [d.local_normalizer]
    exact sup_le L.le_normalizer d.normalizes_L
  have hred:=Three.exists_five_or_noncontained hD213 s hs
    (local_stronglyQuasithin d hH.prop.2.1) hH
    (d.line_le_plane.trans d.plane_le_seed) hF9.V_le_T
    (d.first_normalizer ▸ le_rfl)
    (LocalFitting.intersection_residual d hH.prop hsource)
    (plus_le_one L T V₁ d.line_stable) a (source_kernel hF9) hQ
    h rfl hplace h135 ((one_le L T V₁).trans (inf_le_left.trans hLM))
    (d.local_normalizer ▸ d.normalizes_L) (T_normalizes_one L T V₁ d.line_stable) hseed d.seed_card
  refine ⟨h,hplace,?_⟩
  rcases hred with hf | ⟨r,hout,hsmall⟩
  · exact hf
  · exact (noncontained_three_impossible d hF9 s r hout hsmall a hQ).elim

end OddReduction
end CFSG.Quasithin.Chapter13.Section08.SourceCompletion
