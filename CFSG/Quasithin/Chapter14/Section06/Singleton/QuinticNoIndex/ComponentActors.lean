module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.Intersections
public import Theory.GroupTheory.SylowNormalJoinIntersection

/-!
# Literal component actors before the quintic factor-join index

The component Borel cores split the Sylow intersection with the strict
closure. The original residual preserves both cores, so their join is
normal in J and lies in O₂(J). Consequently the intrinsic component
intersection quotients identify with their actual images in J/O₂(J).
No index for Jhat and no full automorphism-wreath model are assumed.
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
private theorem component_borel_control (T : Sylow 2 G) (J K : Subgroup G)
    (hc : (K ⊓ J).pCoreIn 2 = K ⊓ (T : Subgroup G)) :
    J ⊓ normalizer (K : Set G) ≤
      normalizer ((K ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
  rw [←hc]
  exact ((le_inf inf_le_right (inf_le_left.trans J.le_normalizer)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (K ⊓ J) (pCore 2 (K ⊓ J : Subgroup G)))

private theorem closure_normalizes_components (T : Sylow 2 G) {J Mc : Subgroup G}
    (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T)) :
    residualClosure J Mc ≤ normalizer (b.K1 : Set G) ∧
      residualClosure J Mc ≤ normalizer (b.K2 : Set G) := by
  have hR : residualClosure J Mc ≤ residual Mc := by
    apply conjugateSpanBy_le (embedded_pResidual_mono 2 hJM)
    exact Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pResidual 2 Mc))
  exact ⟨hR.trans ((residual_le_of_index_two (Mc ⊓ normalizer (b.K1 : Set G))
      inf_le_left b.first_index).trans inf_le_right),
    hR.trans ((residual_le_of_index_two (Mc ⊓ normalizer (b.K2 : Set G))
      inf_le_left b.second_index).trans inf_le_right)⟩

private theorem closure_sylow_split (T : Sylow 2 G) {J Mc : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T)) :
    (T : Subgroup G) ⊓ residualClosure J Mc =
      (b.K1 ⊓ (T : Subgroup G)) ⊔ (b.K2 ⊓ (T : Subgroup G)) := by
  let Kz := residualClosure J Mc
  have hKM : Kz ≤ Mc := by
    change residualClosure J Mc ≤ Mc
    rw [←b.join_eq]
    exact sup_le b.first_le b.second_le
  have hn := closure_normalizes_components T hJM b
  have h1 : b.K1 ≤ Kz := (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ Kz := (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  let KM := Kz.subgroupOf Mc
  let K1M := b.K1.subgroupOf Mc
  let K2M := b.K2.subgroupOf Mc
  let : KM.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : (K1M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hh : x ∈ (normalizer (b.K1 : Set G)).subgroupOf Mc := hn.1 hx
    rwa [subgroupOf_normalizer_eq b.first_le] at hh)
  let : (K2M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hh : x ∈ (normalizer (b.K2 : Set G)).subgroupOf Mc := hn.2 hx
    rwa [subgroupOf_normalizer_eq b.second_le] at hh)
  have hj : K1M ⊔ K2M = KM := by
    rw [←subgroupOf_sup b.first_le b.second_le,b.join_eq]
  have hTM := hTJ.trans hJM
  have hh := (T.subtype hTM).inf_sup_eq_sup_inf_relative KM K1M K2M
    (fun x hx => h1 hx) (fun x hx => h2 hx) hj
  have hm := congrArg (Subgroup.map Mc.subtype) hh
  dsimp only [KM,K1M,K2M] at hm
  have hTm : ((T.subtype hTM : Sylow 2 Mc) : Subgroup Mc).map Mc.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTM
  simp only [Subgroup.map_sup,Subgroup.map_inf _ _ _ Mc.subtype_injective,
    hTm,map_subgroupOf_eq_of_le hKM,
    map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] at hm
  simpa only [inf_comm] using hm

private theorem closure_sylow_le_core (T : Sylow 2 G) {J Mc : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J) (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T))
    (hc1 : (b.K1 ⊓ J).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G))
    (hc2 : (b.K2 ⊓ J).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G)) :
    (T : Subgroup G) ⊓ residualClosure J Mc ≤ J.pCoreIn 2 := by
  have hn := closure_normalizes_components T hJM b
  have hR1 : residual J ≤ normalizer ((b.K1 ⊓ (T : Subgroup G) : Subgroup G) : Set G) :=
    (le_inf (residual_le J) ((le_conjugateSpanBy _ _).trans hn.1)).trans
      (component_borel_control T J b.K1 hc1)
  have hR2 : residual J ≤ normalizer ((b.K2 ⊓ (T : Subgroup G) : Subgroup G) : Set G) :=
    (le_inf (residual_le J) ((le_conjugateSpanBy _ _).trans hn.2)).trans
      (component_borel_control T J b.K2 hc2)
  have hRT : residual J ⊔ (T : Subgroup G) = J := by
    have hh := congrArg (Subgroup.map J.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hTJ))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change residual J ⊔ (((T : Subgroup G).subgroupOf J).map J.subtype) = J at hh
    rwa [map_subgroupOf_eq_of_le hTJ] at hh
  have hR : residual J ≤
      normalizer (((T : Subgroup G) ⊓ residualClosure J Mc : Subgroup G) : Set G) := by
    rw [closure_sylow_split T hTJ hJM b]
    exact (le_inf hR1 hR2).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hT : (T : Subgroup G) ≤
      normalizer (((T : Subgroup G) ⊓ residualClosure J Mc : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      ((hTJ.trans hJM).trans (le_normalizer_conjugateSpanBy _ _))).trans
        inf_normalizer_le_normalizer_inf
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
    (inf_le_left.trans hTJ) (hRT.ge.trans (sup_le hR hT))

omit [Finite G] in
private theorem component_core_intersection (T : Sylow 2 G) {J Mc K : Subgroup G}
    (hTJ : (T : Subgroup G) ≤ J)
    (hQ : (T : Subgroup G) ⊓ residualClosure J Mc ≤ J.pCoreIn 2)
    (hK : K ≤ residualClosure J Mc) :
    K ⊓ J.pCoreIn 2 = K ⊓ (T : Subgroup G) := by
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := J.pCoreIn_le_sylow (T.subtype hTJ)
    change J.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf J).map J.subtype at hh
    rwa [map_subgroupOf_eq_of_le hTJ] at hh
  exact le_antisymm (inf_le_inf_left _ hQT)
    (le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hK)).trans hQ))

omit [Finite G] in
private theorem component_actor_quotient (T : Sylow 2 G) {J K : Subgroup G}
    (hc : (K ⊓ J).pCoreIn 2 = K ⊓ (T : Subgroup G))
    (hi : K ⊓ J.pCoreIn 2 = K ⊓ (T : Subgroup G)) :
    ∃ e : ((K ⊓ J : Subgroup G) ⧸ pCore 2 (K ⊓ J : Subgroup G)) ≃* actorImage J K,
      ∀ x : (K ⊓ J : Subgroup G),
        (e (QuotientGroup.mk' (pCore 2 (K ⊓ J : Subgroup G)) x) : J ⧸ pCore 2 J) =
          QuotientGroup.mk' (pCore 2 J) ⟨x,x.property.2⟩ := by
  let B := K ⊓ J
  let q := QuotientGroup.mk' (pCore 2 J)
  let f0 : B →* J ⧸ pCore 2 J := q.comp (inclusion (show B ≤ J from inf_le_right))
  let f : B →* actorImage J K := f0.codRestrict _
    (fun x => mem_map_of_mem q x.property.1)
  have hf : Function.Surjective f := by
    rintro ⟨x,hx⟩
    obtain ⟨y,hy,rfl⟩ := hx
    exact ⟨⟨y,hy,y.property⟩,rfl⟩
  have hk : f.ker = pCore 2 B := by
    ext x
    have hx : x ∈ pCore 2 B ↔ (x : G) ∈ K ⊓ (T : Subgroup G) := by
      rw [←hc]
      exact (mem_map_iff_mem B.subtype_injective).symm
    have hq : q ⟨(x : G),x.property.2⟩ = 1 ↔ (x : G) ∈ J.pCoreIn 2 := by
      exact (QuotientGroup.eq_one_iff (N := pCore 2 J) ⟨(x : G),x.property.2⟩).trans
        (mem_map_iff_mem J.subtype_injective).symm
    change f x = 1 ↔ x ∈ pCore 2 B
    rw [hx,←hi]
    constructor
    · intro he
      exact ⟨x.property.1,hq.mp (congrArg Subtype.val he)⟩
    · intro he
      exact Subtype.ext (hq.mpr he.2)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact ⟨e,fun x => rfl⟩

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

/-- The strict original branch supplies both literal quintic actor images,
with the exact intrinsic quotient maps and the original Sylow cores. -/
theorem source_quintic_strict_component_actors
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T),
      (T : Subgroup G) ⊓ residualClosure J Mc ≤ J.pCoreIn 2 ∧
      (b.K1 ⊓ J).pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
      (b.K2 ⊓ J).pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
      b.K1 ⊓ J.pCoreIn 2 = b.K1 ⊓ (T : Subgroup G) ∧
      b.K2 ⊓ J.pCoreIn 2 = b.K2 ⊓ (T : Subgroup G) ∧
      Nat.card (actorImage J b.K1) = 5 ∧ Nat.card (actorImage J b.K2) = 5 ∧
      (∃ e1 : ((b.K1 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K1 ⊓ J : Subgroup G)) ≃*
          actorImage J b.K1,
        ∀ x : (b.K1 ⊓ J : Subgroup G),
          (e1 (QuotientGroup.mk' (pCore 2 (b.K1 ⊓ J : Subgroup G)) x) : J ⧸ pCore 2 J) =
            QuotientGroup.mk' (pCore 2 J) ⟨x,x.property.2⟩) ∧
      (∃ e2 : ((b.K2 ⊓ J : Subgroup G) ⧸ pCore 2 (b.K2 ⊓ J : Subgroup G)) ≃*
          actorImage J b.K2,
        ∀ x : (b.K2 ⊓ J : Subgroup G),
          (e2 (QuotientGroup.mk' (pCore 2 (b.K2 ⊓ J : Subgroup G)) x) : J ⧸ pCore 2 J) =
            QuotientGroup.mk' (pCore 2 J) ⟨x,x.property.2⟩) := by
  obtain ⟨b,hc1,hc2,h5a,h5b⟩ := source_quintic_strict_component_intersections
    hG T hempty hM hu hmany hcard e hab J hJ hs a f d π w hne
  have hJM : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hQ := closure_sylow_le_core T hJ.1.1.2 hJM b hc1 hc2
  have hi1 := component_core_intersection T hJ.1.1.2 hQ
    ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq)
  have hi2 := component_core_intersection T hJ.1.1.2 hQ
    ((le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq)
  obtain ⟨e1,he1⟩ := component_actor_quotient T hc1 hi1
  obtain ⟨e2,he2⟩ := component_actor_quotient T hc2 hi2
  exact ⟨b,hQ,hc1,hc2,hi1,hi2,(Nat.card_congr e1.toEquiv).symm.trans h5a,
    (Nat.card_congr e2.toEquiv).symm.trans h5b,⟨e1,he1⟩,⟨e2,he2⟩⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
