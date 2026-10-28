module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ComponentActorProduct

/-!
# Component normalizers detected in the original quintic quotient

Exchanging the actual components exchanges their distinct quintic images
in J/O₂(J). Thus preservation of the first image detects its component
normalizer. In particular O₂(J) preserves both components, without a
factor-join index or an assumed component action.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer
open OddNormalizer.Quintic.ModuleGeometry (ExchangedFactorData)
namespace Singleton.QuinticNoIndex
open SourcePairCompatibility.QuinticGeometryParallel
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem actorImage_intersection {J : Subgroup G} (K : Subgroup G) :
    actorImage J (K ⊓ J) = actorImage J K := by
  unfold actorImage
  congr 1
  ext x
  exact and_iff_left x.property

omit [Finite G] in
private theorem actorImage_conjugate_any {J : Subgroup G} (K : Subgroup G) (h : J) :
    actorImage J (K.map (MulAut.conj (h : G)).toMonoidHom) =
      (actorImage J K).map (MulAut.conj (QuotientGroup.mk' (pCore 2 J) h)).toMonoidHom := by
  have hh := actorImage_conjugate (K ⊓ J) inf_le_right h
  have hH : J.map (MulAut.conj (h : G)).toMonoidHom = J :=
    mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer h.property)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (h : G)).injective,hH,
    actorImage_intersection,actorImage_intersection] at hh
  exact hh

omit [Finite G] in
private theorem first_actor_normalizer (T : Sylow 2 G) {J Mc : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T))
    (hcard1 : Nat.card (actorImage J b.K1) = 5)
    (hdis : Disjoint (actorImage J b.K1) (actorImage J b.K2)) (x : J) :
    (x : G) ∈ normalizer (b.K1 : Set G) ↔
      QuotientGroup.mk' (pCore 2 J) x ∈ normalizer (actorImage J b.K1 : Set (J ⧸ pCore 2 J)) := by
  constructor
  · intro hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : b.K1.map (MulAut.conj (x : G)).toMonoidHom = b.K1 :=
      mem_normalizer_iff_map_conj_eq.mp hx
    exact (actorImage_conjugate_any b.K1 x).symm.trans (congrArg (actorImage J) he)
  · intro hx
    by_contra hn
    obtain ⟨t,ht,htn,he⟩ := b.exchanged
    have hex := map_conj_eq_of_outside_normalizer J Mc
      (Mc ⊓ normalizer (b.K1 : Set G)) b.K1 b.K2 hJM
      b.first_le b.first_index inf_le_right t (hTJ ht) htn he
      x x.property (fun h => hn h.2)
    have hi := actorImage_conjugate_any (J := J) b.K1 x⁻¹
    have hqi : (actorImage J b.K1).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 J) x)⁻¹).toMonoidHom = actorImage J b.K1 :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem hx)
    change actorImage J (b.K1.map (MulAut.conj (x : G)⁻¹).toMonoidHom) =
      (actorImage J b.K1).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 J) x⁻¹)).toMonoidHom at hi
    rw [hex,map_inv,hqi] at hi
    have hd := hdis
    rw [hi] at hd
    have hb : actorImage J b.K1 = ⊥ := disjoint_self.mp hd
    have hc := hcard1
    rw [hb,card_bot] at hc
    omega

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
    (w : SourcePairCompatibility.QuinticOuterAction a f d π)
include hG hempty hM hu hmany hcard e hab hJ hs w

/-- The original two-core preserves both actual components. Membership
in the first component normalizer is detected by its literal quotient actor. -/
theorem source_quintic_strict_component_normalizers
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T),
      Nat.card (actorImage J b.K1) = 5 ∧ Nat.card (actorImage J b.K2) = 5 ∧
      Disjoint (actorImage J b.K1) (actorImage J b.K2) ∧
      actorImage J b.K1 ⊔ actorImage J b.K2 = pResidual 2 (J ⧸ pCore 2 J) ∧
      (∀ x : J, (x : G) ∈ normalizer (b.K1 : Set G) ↔
        QuotientGroup.mk' (pCore 2 J) x ∈
          normalizer (actorImage J b.K1 : Set (J ⧸ pCore 2 J))) ∧
      J.pCoreIn 2 ≤ normalizer (b.K1 : Set G) ∧
      J.pCoreIn 2 ≤ normalizer (b.K2 : Set G) := by
  obtain ⟨b,hc1,hc2,hjoin,hdis,_ep⟩ := source_quintic_strict_component_actor_product
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  have hJM : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hn := first_actor_normalizer T hJ.1.1.2 hJM b hc1 hdis
  have hfirst : J.pCoreIn 2 ≤ normalizer (b.K1 : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    apply (hn x).mpr
    have he : QuotientGroup.mk' (pCore 2 J) x = 1 :=
      (QuotientGroup.eq_one_iff (N := pCore 2 J) x).mpr hx
    rw [he]
    exact one_mem _
  refine ⟨b,hc1,hc2,hdis,hjoin,hn,hfirst,?_⟩
  obtain ⟨t,ht,_,he⟩ := b.exchanged
  rw [←he,←map_equiv_normalizer_eq b.K1 (MulAut.conj t⁻¹)]
  have hm := map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) hfirst
  have hQ : (J.pCoreIn 2).map (MulAut.conj t⁻¹).toMonoidHom = J.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      ((normalizer_le_normalizer_characteristic_image J (pCore 2 J))
        (J.le_normalizer (J.inv_mem (hJ.1.1.2 ht))))
  rwa [hQ] at hm

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
