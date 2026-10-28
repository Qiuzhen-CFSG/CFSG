module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairedPointCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingPointFlags

/-!
# The original vector kernel in the paired point-Borel marking

The point-centralizer equivalence retains the original block-module coordinates.
Its vector subgroup therefore maps to the literal source module. This fixes the
lower kernel used by the paired four-group quotient in original 14.6.9(l).

Source: Aschbacher--Smith, 14.6.9(i,l), printed p.1027; the marked splitting
is the natural alternating-five extension of C.5.6.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section06
open Subgroup Theory.GroupTheory Stellmacher
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open BinaryPermutation BinaryPermutation.AlternatingFiveExtension
variable {G : Type*} [Group G] [Finite G]

/-- The Borel equivalence identifies its vector kernel with the actual block module. -/
theorem source_paired_block_borel_vectors
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (Λ : Subgroup G)
    (c : OriginalHypotheses I Λ ((pResidual 2 I).map I.subtype)
      ((T : Subgroup G) ⊓ I) ((T : Subgroup G) ⊓ I))
    (b : OrbitDecomposition (c.sylow : Subgroup I)
      (((T : Subgroup G) ⊓ I).subgroupOf I) (pResidual 2 I))
    (i j : Fin b.size) (hij : i ≠ j) (hs : b.size = 2)
    (hi : IsAlternatingBlock ((b.block i).map I.subtype) 5) :
    ∃ eb : ((b.block i).map I.subtype ⊓ Mc : Subgroup G) ≃* BorelModel,
      PointCoreGeometry.vectors.map
        (((b.block i).map I.subtype ⊓ Mc).subtype.comp eb.symm.toMonoidHom) =
          sourceModule ((b.block i).map I.subtype) := by
  obtain ⟨z,hz,heq,hzS,hzC,hout,h,v,hv,hcentral,hpoint⟩ := source_paired_block_point_marking
    hG T hempty hM hunique hmany hcard e hab H hH u hu I hI Λ c b i j hij hs hi
  obtain ⟨x,hx,hcomm⟩ := c.exists_noncommuting_module b i
  have hnc : ¬ (sourceModule ((b.block i).map I.subtype)).map
      (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule ((b.block i).map I.subtype) : Set G) := by
    rw [ambientModule_eq_literal] at hcomm
    exact fun hh => hcomm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  obtain ⟨eb,heb⟩ := h.central_point_borel_marked x (c.R_normal hx) hnc z hzS hzC (heq.symm ▸ hout)
  let ef : ((b.block i).map I.subtype ⊓ Mc : Subgroup G) ≃* BorelModel :=
    (MulEquiv.subgroupCongr (congrArg
      (fun C : Subgroup G => (b.block i).map I.subtype ⊓ C) heq.symm)).trans eb
  refine ⟨ef,?_⟩
  let f := ((b.block i).map I.subtype ⊓ Mc).subtype.comp ef.symm.toMonoidHom
  have hfi : f.comp SemidirectProduct.inl = h.borelMap := MonoidHom.ext heb
  change PointCoreGeometry.vectors.map f = _
  rw [PointCoreGeometry.vectors,←SemidirectProduct.range_inl_eq_ker_rightHom,
    MonoidHom.map_range,hfi]
  change ((sourceModule ((b.block i).map I.subtype)).subtype.comp
    h.coordinates.symm.toMonoidHom).range = _
  rw [MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _ h.coordinates.symm.surjective,
    ←MonoidHom.range_eq_map]
  exact (sourceModule ((b.block i).map I.subtype)).range_subtype

end CFSG.Quasithin.Chapter14.Section06
