module
public import CFSG.Quasithin.Chapter14.Section06.SourcePairCompatibility.QuinticGeometryParallel.ResidualPlane
public import Theory.GroupTheory.PResidual.QuinticPairControl
public import Theory.GroupTheory.ConjugateOrbitIndexTwoStabilizer

/-!
# The ordinary quintic point closure in the no-index residual branch

When the residual is normal in Mc, its two literal factors are subnormal,
two-perfect, and have cyclic-five core quotients. The actual primitive plane
has five-rank two. If the second-factor normalizer has index two in Mc,
quintic-pair control puts every element of order five in the residual.
Prime-order generation and Mc = C_G(Z) identify the ordinary point closure.

The index assumption is in Mc, not the index of Jhat in J/O₂(J).
Source: Aschbacher--Smith 14.6.15, printed p.1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
namespace SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem subtype_conjugate_map (J : Subgroup G) (A : Subgroup J) (t : J) :
    (A.map (MulAut.conj t).toMonoidHom).map J.subtype =
      (A.map J.subtype).map (MulAut.conj (t:G)).toMonoidHom := by
  rw [map_map,map_map]
  rfl

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

/-- In the residual branch, the ambient index and five-rank bound confine
all quintic elements of Mc to the actual residual of J. -/
theorem source_quintic_residual_quintic_elements (hd : d.FittingFull)
    (hc : residualClosure J Mc = residual J)
    (hindex : ∀ k : d.Index, (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2)
    {x : G} (hx : x ∈ Mc) (ho : orderOf x = 5) : x ∈ residual J := by
  have hmore : 1 < Nat.card d.Index := by rw [w.two_factors]; decide
  obtain ⟨_,p,m,_hpm,_hmark,_hmarked,i,j,hij,_hall,_hjoin,_hdis,_hcom,_hspace,_hspaceDis,
    _hfixed,_hsupport,_hpoint,t,htT,_ha,_ha',_hsp,_hnq,htij,_htn⟩ :=
    source_ratio_nonsingleton_dihedral hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d hd hmore
  let H1 := actorPreimage J (f.ambientFactor d i).actor
  let H2 := actorPreimage J (f.ambientFactor d j).actor
  have hjoin : residual H1 ⊔ residual H2 = residual J :=
    source_quintic_residual_join_of_ne hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w i j hij
  have hHM : J ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
      J hJ.1.1 hJ.1.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hTMc : (T : Subgroup G) ≤ Mc := hJ.1.1.2.trans hHM
  have he : H1.map (MulAut.conj (t:G)).toMonoidHom = H2 :=
    (subtype_conjugate_map J ((f.ambientFactor d i).actor.comap
      (QuotientGroup.mk' (pCore 2 J))) t).symm.trans (congrArg (map J.subtype) htij)
  have hr : (residual H1).map (MulAut.conj (t:G)).toMonoidHom = residual H2 := by
    unfold GenerationOne.residual
    rw [map_embedded_pResidual,he]
  have hback : (residual H2).map (MulAut.conj (t:G)⁻¹).toMonoidHom = residual H1 := by
    rw [←hr]
    exact conjBy_inv _ (t:G)
  have hi : (Mc ⊓ normalizer (residual H2 : Set G)).relIndex Mc = 2 := hindex j
  have hfirst : Mc ⊓ normalizer (residual H2 : Set G) ≤ normalizer (residual H1 : Set G) := by
    have hi' : (normalizer (residual H2 : Set G)).relIndex Mc = 2 := by
      simpa only [inf_relIndex_left] using hi
    have hh := index_two_stabilizer_normalizes_conjugate (residual H2) Mc hi'
      (hTMc ((T : Subgroup G).inv_mem htT))
    rwa [hback] at hh
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := (residual H1).subgroupOf Mc
  let B := (residual H2).subgroupOf Mc
  have h1 : residual H1 ≤ Mc := (residual_le H1).trans ((actorPreimage_le J _).trans hHM)
  have h2 : residual H2 ≤ Mc := (residual_le H2).trans ((actorPreimage_le J _).trans hHM)
  have hKM : residual J ≤ Mc := (residual_le J).trans hHM
  have hj : A ⊔ B = (residual J).subgroupOf Mc := by
    rw [←hjoin,subgroupOf_sup h1 h2]
  have hA : A.IsSubnormal := source_quintic_residual_subnormal hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w hc i
  have hB : B.IsSubnormal := source_quintic_residual_subnormal hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π hp w hc j
  let eA := subgroupOfEquivOfLe h1
  let eB := subgroupOfEquivOfLe h2
  let eK := subgroupOfEquivOfLe hKM
  have hcA : Nat.card (A ⧸ pCore 2 A) = 5 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eA (pCore_map_iso 2 eA)).toEquiv).trans
      ((Nat.card_congr (source_quintic_factor_residual_model T J a f d π w i).some.toEquiv).trans (by simp))
  have hcB : Nat.card (B ⧸ pCore 2 B) = 5 :=
    (Nat.card_congr (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).toEquiv).trans
      ((Nat.card_congr (source_quintic_factor_residual_model T J a f d π w j).some.toEquiv).trans (by simp))
  have hnA : normalizer (B : Set Mc) ≤ normalizer (A : Set Mc) := by
    rw [←subgroupOf_normalizer_eq h1,←subgroupOf_normalizer_eq h2]
    intro y hy
    exact hfirst ⟨y.property,hy⟩
  have hiB : (normalizer (B : Set Mc)).index = 2 := by
    rw [←subgroupOf_normalizer_eq h2]
    change (normalizer (residual H2 : Set G)).relIndex Mc = 2
    simpa only [inf_relIndex_left] using hi
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  have hrank : primeRank 5 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hmax.1).stronglyQuasithin 5 (by decide) (by decide)
  let := (source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w).elementary
  obtain ⟨eq,_⟩ := residual_quotient_equiv (by decide : Odd 5) J
    (IsElementaryAbelian.isPGroup 5 (pResidual 2 (J ⧸ pCore 2 J)))
  let : IsElementaryAbelian 5 (Chapter1.XiQuotient (residual J)) :=
    IsElementaryAbelian.of_surjective eq.symm.toMonoidHom eq.symm.surjective
  let : IsElementaryAbelian 5 (⊤ : Subgroup (Chapter1.XiQuotient (residual J))) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup (Chapter1.XiQuotient (residual J))).subtype
      (⊤ : Subgroup (Chapter1.XiQuotient (residual J))).subtype_injective
  have hrQ : 2 ≤ primeRank 5 (Chapter1.XiQuotient (residual J)) := by
    apply IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup (Chapter1.XiQuotient (residual J)))
    rw [Nat.card_congr Subgroup.topEquiv.toEquiv,Nat.card_congr eq.toEquiv,
      source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w]
    norm_num
  have hrK : primeRank 5 (A ⊔ B : Subgroup Mc) = 2 := by
    rw [hj,primeRank_congr 5 eK]
    exact le_antisymm ((primeRank_mono 5 hKM).trans hrank)
      (hrQ.trans (primeRank_quotient_le_of_isTwoGroup 5 (by decide) _ pCore_isPGroup))
  have hpA : IsPPerfect 2 A := (isPPerfect_embedded_pResidual 2 H1).of_surjective
    eA.symm.toMonoidHom eA.symm.surjective
  have hpB : IsPPerfect 2 B := (isPPerfect_embedded_pResidual 2 H2).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  have hpK : IsPPerfect 2 (A ⊔ B : Subgroup Mc) := by
    rw [hj]
    exact (isPPerfect_embedded_pResidual 2 J).of_surjective eK.symm.toMonoidHom eK.symm.surjective
  have hm := mem_sup_of_order_five_of_index_two_normalizer A B hA hB hcA hcB hiB hnA
    hrank hrK hpA hpB hpK (x := ⟨x,hx⟩) (by rwa [←Subgroup.orderOf_coe])
  have hm' : (⟨x,hx⟩ : Mc) ∈ (residual J).subgroupOf Mc := hj ▸ hm
  exact hm'

/-- The ordinary point-centralizer closure follows from the literal
residual geometry and its ambient index; it is not an extra input. -/
theorem source_quintic_residual_point_closure (hd : d.FittingFull)
    (hc : residualClosure J Mc = residual J)
    (hindex : ∀ k : d.Index, (Mc ⊓ normalizer
      (residual (actorPreimage J (f.ambientFactor d k).actor) : Set G)).relIndex Mc = 2) :
    closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} = residual J := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hu hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJM : J ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hu hmany hcard e
      J hJ.1.1 hJ.1.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups J from he ▸ Set.mem_singleton Mc).2
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact source_quintic_residual_quintic_elements hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π hp w hd hc hindex (hMc.ge hx.1) hx.2
  · obtain ⟨i,j,_hij,_hall,hjoin⟩ := source_quintic_residual_join hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w
    rw [←hjoin]
    have hfactor (k : d.Index) : residual (actorPreimage J (f.ambientFactor d k).actor) ≤
        closure {x : G | x ∈ centralizer (centralInvolutions T : Set G) ∧ orderOf x = 5} := by
      rw [←source_quintic_residual_generated T J a f d π w k]
      apply Subgroup.closure_mono
      intro x hx
      exact ⟨hMc.le (hJM (actorPreimage_le J _ (residual_le _ hx.1))),hx.2⟩
    exact sup_le (hfactor i) (hfactor j)

end SourcePairCompatibility.QuinticGeometryParallel
end CFSG.Quasithin.Chapter14.Section06
