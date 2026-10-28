module
public import CFSG.Quasithin.Chapter14.Section06.Singleton.QuinticNoIndex.ComponentActors
public import Theory.GroupTheory.SylowSubnormalIntersectionIndex

/-!
# The component product in the original quintic residual

The original Sylow-five subgroup stays Sylow in Mc. Its intersections
with the normal component pair generate its image in J/O₂(J), which is
the elementary residual of order twenty-five. The two literal component
images therefore form a direct product, without the index of Jhat.
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

private theorem five_subgroup_le_residual {D : Type*} [Group D] [Finite D]
    (P : Subgroup D) (hP : IsPGroup 5 P) : P ≤ pResidual 2 D := by
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  rw [Subgroup.orderOf_coe (⟨x,hx⟩ : P)]
  exact (hP.orderOf_coprime (by decide : Nat.Coprime 5 2) _).symm

private theorem sylow_five_image_eq_residual {J : Subgroup G}
    [IsElementaryAbelian 5 (pResidual 2 (J ⧸ pCore 2 J))] (P : Sylow 5 J) :
    (P : Subgroup J).map (QuotientGroup.mk' (pCore 2 J)) = pResidual 2 (J ⧸ pCore 2 J) := by
  let R := P.mapSurjective (f := QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)
  apply le_antisymm
  · exact five_subgroup_le_residual _ R.isPGroup'
  · exact (IsElementaryAbelian.isPGroup 5 _).le_sylow_of_normal R

private theorem source_component_sylow_intersections_split
    (T : Sylow 2 G) {J Mc : Subgroup G} (hJM : J ≤ Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T))
    (P : Sylow 5 Mc) :
    (P : Subgroup Mc) ⊓ (residualClosure J Mc).subgroupOf Mc =
      ((P : Subgroup Mc) ⊓ b.K1.subgroupOf Mc) ⊔
      ((P : Subgroup Mc) ⊓ b.K2.subgroupOf Mc) := by
  let KM := (residualClosure J Mc).subgroupOf Mc
  let K1M := b.K1.subgroupOf Mc
  let K2M := b.K2.subgroupOf Mc
  have hR : residualClosure J Mc ≤ residual Mc := by
    apply conjugateSpanBy_le (embedded_pResidual_mono 2 hJM)
    exact Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pResidual 2 Mc))
  have hn : residualClosure J Mc ≤ normalizer (b.K1 : Set G) ∧
      residualClosure J Mc ≤ normalizer (b.K2 : Set G) :=
    ⟨hR.trans ((residual_le_of_index_two (Mc ⊓ normalizer (b.K1 : Set G))
        inf_le_left b.first_index).trans inf_le_right),
      hR.trans ((residual_le_of_index_two (Mc ⊓ normalizer (b.K2 : Set G))
        inf_le_left b.second_index).trans inf_le_right)⟩
  have h1 : b.K1 ≤ residualClosure J Mc :=
    (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ residualClosure J Mc :=
    (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  let : KM.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : (K1M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hh : x ∈ (normalizer (b.K1 : Set G)).subgroupOf Mc := hn.1 hx
    rwa [subgroupOf_normalizer_eq b.first_le] at hh)
  let : (K2M.subgroupOf KM).Normal := normal_subgroupOf_of_le_normalizer (by
    intro x hx
    have hh : x ∈ (normalizer (b.K2 : Set G)).subgroupOf Mc := hn.2 hx
    rwa [subgroupOf_normalizer_eq b.second_le] at hh)
  apply P.inf_sup_eq_sup_inf_relative KM K1M K2M
    (fun x hx => h1 hx) (fun x hx => h2 hx)
  rw [←subgroupOf_sup b.first_le b.second_le,b.join_eq]

private theorem component_actor_join
    (T : Sylow 2 G) {J Mc : Subgroup G} (hJM : J ≤ Mc)
    [IsElementaryAbelian 5 (pResidual 2 (J ⧸ pCore 2 J))]
    (hindex : ¬5 ∣ J.relIndex Mc)
    (b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T))
    (hcard1 : Nat.card (actorImage J b.K1) = 5)
    (hcard2 : Nat.card (actorImage J b.K2) = 5) :
    actorImage J b.K1 ⊔ actorImage J b.K2 = pResidual 2 (J ⧸ pCore 2 J) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hA (K : Subgroup G) (hc : Nat.card (actorImage J K) = 5) :
      actorImage J K ≤ pResidual 2 (J ⧸ pCore 2 J) := by
    apply five_subgroup_le_residual
    exact IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hc)
  apply le_antisymm (sup_le (hA _ hcard1) (hA _ hcard2))
  let P : Sylow 5 J := Classical.choice inferInstance
  let eH := subgroupOfEquivOfLe hJM
  let P0 := P.mapSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let PM : Sylow 5 Mc := P0.mapSubtypeOfIndexPrimeTo hindex
  have he : (PM : Subgroup Mc).map Mc.subtype = (P : Subgroup J).map J.subtype := by
    change (((P : Subgroup J).map eH.symm.toMonoidHom).map (J.subgroupOf Mc).subtype).map
      Mc.subtype = _
    rw [map_map,map_map]
    rfl
  have hPK : (PM : Subgroup Mc) ≤ (residualClosure J Mc).subgroupOf Mc := by
    intro x hx
    have hh : (x : G) ∈ (P : Subgroup J).map J.subtype := he ▸ mem_map_of_mem Mc.subtype hx
    obtain ⟨y,hy,hyx⟩ := hh
    have hr : (y : G) ∈ residual J := mem_map_of_mem J.subtype
      (five_subgroup_le_residual _ P.isPGroup' hy)
    change (x : G) ∈ residualClosure J Mc
    rw [←hyx]
    exact le_conjugateSpanBy (residual J) Mc hr
  have hs := source_component_sylow_intersections_split T hJM b PM
  rw [inf_eq_left.mpr hPK] at hs
  have hgen := congrArg (map Mc.subtype) hs
  rw [he,Subgroup.map_sup,Subgroup.map_inf _ _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,he,
    map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] at hgen
  let D := actorImage J b.K1 ⊔ actorImage J b.K2
  let C := (D.comap (QuotientGroup.mk' (pCore 2 J))).map J.subtype
  have hf (K : Subgroup G) (hK : actorImage J K ≤ D) :
      ((P : Subgroup J).map J.subtype) ⊓ K ≤ C := by
    rintro x ⟨⟨y,hy,hyx⟩,hxK⟩
    refine ⟨y,?_,hyx⟩
    have hyK : y ∈ K.subgroupOf J := by
      change J.subtype y ∈ K
      rw [hyx]
      exact hxK
    exact hK (mem_map_of_mem (QuotientGroup.mk' (pCore 2 J)) hyK)
  have hPC : (P : Subgroup J).map J.subtype ≤ C := by
    rw [hgen]
    exact sup_le (hf _ le_sup_left) (hf _ le_sup_right)
  rw [←sylow_five_image_eq_residual P]
  apply map_le_iff_le_comap.mpr
  intro x hx
  have hh := hPC (mem_map_of_mem J.subtype hx)
  exact (mem_map_iff_mem J.subtype_injective).mp hh

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

/-- The actual component actors split the original elementary quintic
residual, retaining multiplication in the original quotient. -/
theorem source_quintic_strict_component_actor_product
    (hne : residualClosure J Mc ≠ residual J) :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc J (centralInvolutions T),
      Nat.card (actorImage J b.K1) = 5 ∧ Nat.card (actorImage J b.K2) = 5 ∧
      actorImage J b.K1 ⊔ actorImage J b.K2 = pResidual 2 (J ⧸ pCore 2 J) ∧
      Disjoint (actorImage J b.K1) (actorImage J b.K2) ∧
      ∃ ep : actorImage J b.K1 × actorImage J b.K2 ≃* pResidual 2 (J ⧸ pCore 2 J),
        ∀ x y, (ep (x,y) : J ⧸ pCore 2 J) =
          (x : J ⧸ pCore 2 J) * (y : J ⧸ pCore 2 J) := by
  obtain ⟨b,_hQ,_hc1,_hc2,_hi1,_hi2,hA,hB,_e1,_e2⟩ :=
    source_quintic_strict_component_actors hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne
  have hJM : J ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hu)
  have hprim := source_quintic_primitive_residual hG T hempty hM hu hmany hcard e hab
    J hJ hs a f d π w
  let := hprim.elementary
  have hj := component_actor_join T hJM
    (source_quintic_strict_outside_index_primeTo_five hG T hempty hM hu hmany hcard e hab
      J hJ hs a f d π w hne) b hA hB
  have hdis : Disjoint (actorImage J b.K1) (actorImage J b.K2) := by
    let A := actorImage J b.K1
    let B := actorImage J b.K2
    have hd : Nat.card (A ⊓ B : Subgroup (J ⧸ pCore 2 J)) ∣ 5 :=
      hA ▸ card_dvd_of_le (show A ⊓ B ≤ A from inf_le_left)
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hc | hc
    · exact disjoint_iff.mpr (card_eq_one.mp hc)
    · have heA : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by rw [hc,hA])
      have heB : A ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by rw [hc,hB])
      change A ⊔ B = pResidual 2 (J ⧸ pCore 2 J) at hj
      rw [←heB,heA,sup_idem] at hj
      have h25 := source_quintic_residual_plane_card hG T hempty hM hu hmany hcard e hab
        J hJ hs a f d π w
      rw [←hj,hA] at h25
      omega
  have h1 : actorImage J b.K1 ≤ pResidual 2 (J ⧸ pCore 2 J) :=
    (le_sup_left : actorImage J b.K1 ≤ actorImage J b.K1 ⊔ actorImage J b.K2).trans_eq hj
  have h2 : actorImage J b.K2 ≤ pResidual 2 (J ⧸ pCore 2 J) :=
    (le_sup_right : actorImage J b.K2 ≤ actorImage J b.K1 ⊔ actorImage J b.K2).trans_eq hj
  have hc : actorImage J b.K1 ≤ centralizer (actorImage J b.K2 : Set (J ⧸ pCore 2 J)) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨y,h2 hy⟩ : pResidual 2 (J ⧸ pCore 2 J)) ⟨x,h1 hx⟩)
  obtain ⟨ep,hep⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage J b.K1) (actorImage J b.K2) hdis hc
  exact ⟨b,hA,hB,hj,hdis,ep.trans (MulEquiv.subgroupCongr hj),hep⟩

end Singleton.QuinticNoIndex
end CFSG.Quasithin.Chapter14.Section06
