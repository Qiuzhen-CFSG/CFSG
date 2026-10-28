module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.Source
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankOneReversal
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpointTranslations
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.Contracts

/-!
# Literal quintic preimages and the two marked critical points

The no-index quadratic confinement places the actual critical actor in a
D10 factor. Its rank-one denominator and displacement of at least two force
the opposite central line into that factor's full covering support. Reversal
and the actual factor permutation give the second point containment; a right
translation aligns the two labels without changing the actor or first point.

Source: Aschbacher--Smith 14.6.13(2), printed p.1032, and F.9.17, p.324.
This supplies the critical pair before the remaining second-normalizer route.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer OddCriticalPair.Selection
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G]

/-- The literal full preimage of an actor in the original ambient group. -/
def actorPreimage (J : Subgroup G) (A : Subgroup (J ⧸ pCore 2 J)) : Subgroup G :=
  (A.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype

theorem actorImage_actorPreimage (J : Subgroup G) (A : Subgroup (J ⧸ pCore 2 J)) :
    actorImage J (actorPreimage J A) = A := by
  unfold actorPreimage actorImage subgroupOf
  rw [comap_map_eq_self_of_injective J.subtype_injective,
    map_comap_eq_self (by intro x _; exact QuotientGroup.mk'_surjective _ x)]

theorem actorPreimage_le (J : Subgroup G) (A : Subgroup (J ⧸ pCore 2 J)) :
    actorPreimage J A ≤ J := map_subtype_le _

variable [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
variable (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (f : ChapterD.RatioDecomposition.FactorData a.representation
      (ChapterD.Jhat a.representation)
      (subspaceCommutator a.representation ⊤ (pResidual 2 (J ⧸ pCore 2 J))))
    (d : ChapterD.RatioDecomposition.Decomposition f.representation)
    (π : (J ⧸ pCore 2 J) →* Equiv.Perm d.Index)
    (hp : ∀ g i, (f.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom =
      (f.ambientFactor d (π g i)).actor)
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs hp w




/-- The original preimage convention gives the actual first point containment. -/
theorem source_quintic_selected_point :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ c : SelectedQuadraticEndpoint h a,
      ∃ k, actorImage J (c.endpoint.conjugate D.UH) ≤ (f.ambientFactor d k).actor ∧
        c.endpoint.conjugate D.V₁ ≤ firstSupport a (actorPreimage J (f.ambientFactor d k).actor) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  intro c
  obtain ⟨⟨k,hk⟩,_,hr⟩ := source_quintic_selected_confinement hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w c
  let : IsElementaryAbelian 2 (actorImage J (c.endpoint.conjugate D.UH)) := c.quadratic.1.2
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1
  have hBH : c.endpoint.conjugate D.UH ≤ J := c.endpoint.large_le hb
  have hn : D.UH ≤ normalizer (c.endpoint.conjugate D.V₁ : Set G) := by
    have hh := map_mono (f := (MulAut.conj c.endpoint.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hh
    exact (c.endpoint.reverse_le hb).trans hh
  have hC : Nat.card (c.endpoint.conjugate D.V₁) = 2 := by
    change Nat.card (D.V₁.map (MulAut.conj c.endpoint.representative).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj c.endpoint.representative).injective,h.point_card]
  refine ⟨k,hk,?_⟩
  apply point_le_support_of_confined_actor a h.H_centralizes 5 (Or.inr rfl)
    (actorPreimage J (f.ambientFactor d k).actor) _ _
    (by rw [actorImage_actorPreimage]; exact (w.dihedral k).some)
    hBH c.quadratic.1.1
  · rwa [actorImage_actorPreimage]
  · rw [actorImage_actorPreimage,←(f.ambientFactor d k).space_eq_support]
    exact w.dimension k
  · exact hn
  · exact hC
  · exact hr

omit [Finite G] hG hempty hM hu hmany hcard e hab hJ hs w in
/-- The full covering support follows the supplied actual factor permutation. -/
theorem factor_support_conjugate (x : J) (k : d.Index) :
    (firstSupport a (actorPreimage J (f.ambientFactor d k).actor)).map
        (MulAut.conj (x : G)).toMonoidHom =
      firstSupport a (actorPreimage J
        (f.ambientFactor d (π (QuotientGroup.mk' (pCore 2 J) x) k)).actor) := by
  unfold firstSupport
  rw [actorImage_actorPreimage,actorImage_actorPreimage,
    supportPreimage_conjugate a _ x,moved_map_conjugate,hp]

/-- The reverse point uses the same conjugator and the literal preimages.
The product in J from F.9.17 accounts for the change of factor label. -/
theorem source_quintic_reverse_point :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    ∀ c : SelectedQuadraticEndpoint h a,
      ∃ k, D.V₁ ≤ c.endpoint.conjugate
        (firstSupport a (actorPreimage J (f.ambientFactor d k).actor)) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  intro c
  obtain ⟨_,hr,hd⟩ := source_quintic_selected_confinement hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w c
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1
  obtain ⟨r,_,hprod,_,_⟩ := c.rank_one_reversal hb hr hd
  obtain ⟨k,_,hpoint⟩ := source_quintic_selected_point hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w r
  let x : J := ⟨(r.endpoint.representative*c.endpoint.representative)⁻¹,J.inv_mem hprod⟩
  refine ⟨π (QuotientGroup.mk' (pCore 2 J) x) k,?_⟩
  have hx : r.endpoint.representative⁻¹ = c.endpoint.representative*(x:G) := by
    dsimp [x]; group
  have hm := map_mono (f := (MulAut.conj r.endpoint.representative⁻¹).toMonoidHom) hpoint
  rw [show (r.endpoint.conjugate D.V₁).map
    (MulAut.conj r.endpoint.representative⁻¹).toMonoidHom = D.V₁ from
      conjBy_inv D.V₁ r.endpoint.representative,hx] at hm
  have ht := hm.trans_eq (conjBy_mul
    (firstSupport a (actorPreimage J (f.ambientFactor d k).actor))
    c.endpoint.representative (x:G))
  change D.V₁ ≤ ((firstSupport a (actorPreimage J (f.ambientFactor d k).actor)).map
    (MulAut.conj (x:G)).toMonoidHom).map (MulAut.conj c.endpoint.representative).toMonoidHom at ht
  rw [factor_support_conjugate T J a f d π hp x k] at ht
  exact ht


omit hp in
/-- The original quintic source selects a strict quadratic endpoint. The
returned-line alternative contradicts its already proved cubic ratio two. -/
theorem source_quintic_selected_exists (hd : d.FittingFull) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    Nonempty (SelectedQuadraticEndpoint h a) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  rcases source_rankTwo_endpoint_selection hG T hempty hM hu hmany hcard e hab J hJ.1 a with
    ⟨l,_⟩ | ⟨c,_⟩
  · obtain ⟨t,_,hne,h2,hr⟩ := l.transvection a h.H_centralizes h.point_card
    have ho : orderOf t = 2 := orderOf_eq_prime h2 hne
    obtain ⟨he,hrank,hquad,_⟩ := involution_actor_rank_and_fixedCodim a.representation t ho
    have hq := QuinticGeometry.source_quintic_pair_ratio_two
      hG T hempty hM hu hmany hcard e hab J hJ hs a f d hd π w
    have hl : (2 : ENNReal) ≤ fixedCodim a.representation (zpowers t) := by
      have hh : cubicRatio a.representation ≤ actionRatio a.representation (zpowers t) :=
        iInf_le_of_le (zpowers t) (iInf_le_of_le ⟨he,isCubic_of_isQuadratic hquad⟩ le_rfl)
      simpa only [hq,actionRatio,hrank,Nat.cast_one,div_one] using hh
    have hl' : 2 ≤ fixedCodim a.representation (zpowers t) := by exact_mod_cast hl
    rw [fixedCodim_zpowers_eq_displacement_rank] at hl'
    omega
  · exact ⟨c⟩

/-- The literal CriticalPair of the quintic branch, including both points
in the same full factor preimage. Neither the index of Jhat nor equality
with the factor-permutation kernel is assumed. -/
theorem source_quintic_critical_pair (hd : d.FittingFull) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis
      hG T hempty hM hu hmany hcard e hab J hJ.1
    ∃ k, Nonempty (Quintic.CriticalPair h a Mc (actorPreimage J (f.ambientFactor d k).actor)) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hu hmany hcard e hab J hJ.1
  change ∃ k, Nonempty (Quintic.CriticalPair h a Mc (actorPreimage J (f.ambientFactor d k).actor))
  obtain ⟨c⟩ : Nonempty (SelectedQuadraticEndpoint h a) := source_quintic_selected_exists hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w hd
  obtain ⟨k,hactor,hpoint⟩ := source_quintic_selected_point hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w c
  obtain ⟨l,hreverse⟩ := source_quintic_reverse_point hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w c
  obtain ⟨q,hq⟩ := source_ratio_factor_transitive hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp k l
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) q
  let j := c.endpoint.mulRight x
  have hj (K : Subgroup G) : j.conjugate K =
      c.endpoint.conjugate (K.map (MulAut.conj (x:G)).toMonoidHom) :=
    conjBy_mul K c.endpoint.representative (x:G)
  have hU : D.UH.map (MulAut.conj (x:G)).toMonoidHom = D.UH :=
    mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_conjugateSpanBy _ _) x.property)
  have hZ : D.V₁.map (MulAut.conj (x:G)).toMonoidHom = D.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) x.property)
  have hjU : j.conjugate D.UH = c.endpoint.conjugate D.UH := by rw [hj,hU]
  have hjZ : j.conjugate D.V₁ = c.endpoint.conjugate D.V₁ := by rw [hj,hZ]
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab J hJ.1
  refine ⟨k,⟨{
    endpoint := j
    outside := source_rankTwo_critical_not_mem_Mc hG T hempty hM hu hmany hcard e hab J hJ.1 j
    proper_kernel := ?_
    actor_le := ?_
    point_le := ?_
    reverse_point_le := ?_
    moved_rank := ?_ }⟩⟩
  · rw [hjU,h.kernel_UH_eq_QH]
    have hc : commutatorPreimage (c.endpoint.conjugate D.UH) D.UH D.V₁ <
        c.endpoint.conjugate D.UH := c.strict
    have hBH : c.endpoint.conjugate D.UH ≤ D.H := c.endpoint.large_le hb
    rw [OddCriticalPair.critical_denominator_eq h _ hBH] at hc
    exact hc
  · rw [hjU,actorImage_actorPreimage]
    exact hactor
  · rw [hjZ]
    exact hpoint
  · have ht := factor_support_conjugate T J a f d π hp x k
    rw [hq] at ht
    exact hreverse.trans_eq ((congrArg c.endpoint.conjugate ht.symm).trans (hj _).symm)
  · obtain ⟨i,j,_,_,_,_,_,hspace,hdis⟩ := f.two_factor_moved_decomposition d w.two_factors
    have hh := Submodule.finrank_sup_add_finrank_inf_eq
      (f.ambientFactor d i).space (f.ambientFactor d j).space
    rw [hspace,hdis.eq_bot,finrank_bot,add_zero,w.dimension i,w.dimension j] at hh
    rw [←source_rankTwo_whole_moved_eq_residual hG T hempty hM hu hmany hcard e hab J hJ.1 a] at hh
    exact hh

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
