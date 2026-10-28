module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwelve
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.MathieuTwentyThree

/-!
# Small involution displacement excludes the marked Mathieu source actions

The source cubic hypotheses recognize the whole M12, M22 and M23 actions,
including outer elements. Their literal intertwiners transport involution
codimensions. Native M12 has inner codimension four and outer codimension
five; the M22 code and cocode have codimension at least three, and its triple
cover has inner codimension four and outer codimension six. M23 inherits the
M24 code and cocode lower bound. Thus none admits a marked involution moving
at most two dimensions. This is the specialization of B.4.5 used for the
original chief action in 13.5.21; it does not remove rows from Table B.4.5.

Source: Aschbacher--Smith H.11--16, K.4 and 13.5.21.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open _root_.Sporadic.Mathieu MathieuCode
open ComponentRecognition.KnownFFTypes.Sporadic
open ChapterK.SporadicCatalogue.SourceFF
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem codim_zpowers_eq {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] (σ : Representation (ZMod 2) D W)
    (f : G →* D) (E : ρ.Equiv (σ.comp f)) (t : G) :
    fixedCodim ρ (zpowers t) = fixedCodim σ (zpowers (f t)) := by
  simpa only [MonoidHom.map_zpowers] using fixedCodim_map_equivariant ρ σ f
    E.toLinearEquiv (fun g w => LinearMap.congr_fun (E.isIntertwining' g) w) (zpowers t)

/-- Every involution in the original M12 source action moves at least four dimensions. -/
theorem m12_involution_ge_four (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier))
    (t : G) (ht : orderOf t = 2) : 4 ≤ fixedCodim ρ (zpowers t) := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : M12Source.Hypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, cubic_ratio := h.smallCubic }
  obtain ⟨_,f,_,hf,_,_,⟨E⟩⟩ := M12Source.source_native_ambient_equiv ρ hs e
  rw [codim_zpowers_eq _ f E t]
  have hft : orderOf (f t) = 2 := (orderOf_injective f hf t).trans ht
  open ChapterH.Section10To12.M12Calculations in
  by_cases hi : f t ∈ MulAut.innerSubgroup M12
  · obtain ⟨x,hx⟩ := hi
    rw [← hx]
    have ho : orderOf x = 2 :=
      (orderOf_injective _ M12AutomorphismRank.conjugation_injective x).symm.trans
        (hx ▸ hft)
    have hfix := fixedSpace_comp_map Ambient.automorphismRepresentation MulAut.conj (zpowers x)
    rw [Ambient.automorphismRepresentation_inner, MonoidHom.map_zpowers] at hfix
    have hd : fixedCodim Ambient.automorphismRepresentation (zpowers (MulAut.conj x)) = 4 := by
      unfold fixedCodim
      rw [← hfix]
      exact fixedCodim_involution x ho
    exact hd.ge
  · rw [LocalActors.fixedCodim_native_outer outer_involution_fusion
      Ambient.automorphismRepresentation Ambient.automorphismRepresentation_faithful hi hft]
    decide

/-- Both simple M22 source markings preserve the native lower displacement bound. -/
theorem m22_involution_ge_three (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier))
    (t : G) (ht : orderOf t = 2) : 3 ≤ fixedCodim ρ (zpowers t) := by
  have hs : M22Source.SourceHypotheses ρ L := {
    sqtk := h.sqtk, component := h.fitting.symm, quasisimple := h.quasisimple,
    faithful := h.faithful, irreducible := h.irreducible, cubic := h.smallCubic,
    quotient := he }
  rcases M22Source.source_markedModels ρ L hs with hc | hd | hD
  · obtain ⟨D⟩ := hc
    rw [codim_zpowers_eq _ D.embedding D.equivalence t]
    exact (m22Outer_involution_displacement_ge_three _
      ((orderOf_injective D.embedding D.injective t).trans ht)).1
  · obtain ⟨D⟩ := hd
    rw [codim_zpowers_eq _ D.embedding D.equivalence t]
    exact (m22Outer_involution_displacement_ge_three _
      ((orderOf_injective D.embedding D.injective t).trans ht)).2
  · obtain ⟨D⟩ := hD
    rw [codim_zpowers_eq _ D.embedding D.equivalence t]
    have hdt : orderOf (D.embedding t) = 2 :=
      (orderOf_injective D.embedding D.injective t).trans ht
    by_cases hi : D.embedding t ∈ Janko4.InvolutionCentralizers.First.QuotientExtension.coverSubgroup
    · rw [← Janko4.InvolutionCentralizers.First.QuotientExtension.coverInclusion_range] at hi
      obtain ⟨x,hx⟩ := hi
      have hxi : Function.Injective Janko4.InvolutionCentralizers.First.QuotientExtension.coverInclusion := Subgroup.inclusion_injective _
      have ho : orderOf x = 2 :=
        (orderOf_injective _ hxi x).symm.trans (hx ▸ hdt)
      rw [← hx]
      have hd := fixedCodim_map_equivariant M22TripleCover.binaryRepresentation
        M22TripleCover.Ambient.binaryAction Janko4.InvolutionCentralizers.First.QuotientExtension.coverInclusion
        (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers x)
      rw [MonoidHom.map_zpowers, M22TripleCover.NoFF.binaryCodim_involution x ho] at hd
      omega
    · rw [M22TripleCover.NoFF.outer_binaryCodim _ hdt hi]
      decide

/-- M23's original code or cocode source marking has no involution of displacement at most two. -/
theorem m23_involution_gt_two (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier))
    (t : G) (ht : orderOf t = 2) : 2 < fixedCodim ρ (zpowers t) := by
  rcases h.fitting with rfl
  obtain ⟨e⟩ := he
  have hs : LargeMathieu.SourceHypotheses ρ := {
    sqtk := h.sqtk, quasisimple := h.quasisimple, faithful := h.faithful,
    irreducible := h.irreducible, cubic_le_two := h.smallCubic }
  obtain ⟨_,_,hc | hd⟩ := LargeMathieu.source_m23_of_degree_and_small_recognition
    m23_degree_eleven LargeMathieu.m23SmallRecognition ρ hs e
  · obtain ⟨f,E,hE⟩ := hc
    have heq := fixedCodim_map_equivariant ρ codeRepresentation
      (pointEmbedding.comp f.toMonoidHom) E hE (zpowers t)
    rw [MonoidHom.map_zpowers, code_cocode_fixedCodim_zpowers] at heq
    rw [heq]
    exact QuadraticActors.m24_cocode_involution_gt_two _
      ((orderOf_injective (pointEmbedding.comp f.toMonoidHom) (pointEmbedding_injective.comp f.injective) t).trans ht)
  · obtain ⟨f,E,hE⟩ := hd
    have heq := fixedCodim_map_equivariant ρ cocodeRepresentation
      (pointEmbedding.comp f.toMonoidHom) E hE (zpowers t)
    rw [MonoidHom.map_zpowers] at heq
    rw [heq]
    exact QuadraticActors.m24_cocode_involution_gt_two _
      ((orderOf_injective (pointEmbedding.comp f.toMonoidHom) (pointEmbedding_injective.comp f.injective) t).trans ht)
end CFSG.Quasithin.ChapterB.SmallRatioClassification.Sporadic
