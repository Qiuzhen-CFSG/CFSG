module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedSylow
public import Theory.SpecificGroups.PSL2.SixteenWreathOrder
public import Theory.GroupTheory.SylowSubnormalIntersectionIndex

/-!
# The literal component product in the original elementary quintic residual

A Sylow-five subgroup of H stays Sylow in Mc because H has index prime
to five. Its image in H/O₂(H) is the original elementary residual. Inside
the normal component product K_z its intersections split along the two
normal components. Their images therefore generate that residual. Each
image has order five, so they are disjoint. Multiplication gives the actual
direct-product isomorphism, with its evaluation formula retained.

The final consumer constructs the decomposition from Context alone.
Identification with the two original dihedral factors still requires the
source module argument; this product statement does not assert it. That
alignment, the opposite-support centralizations, the conjugated point
centralizer and p=3 assembly remain with qt-e-14615-quintic-exclusion.
The allowed earlier 14.6.12--14 inputs and their original owners remain
unchanged, including qt-e-14612-singleton's factor-join index.
Source: Aschbacher--Smith 14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
private theorem original_H_le_partner : H ≤ Mc := by
  have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action H s.outside.1 s.outside.2).1
  exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2

private theorem five_subgroup_le_residual {D : Type*} [Group D] [Finite D]
    (P : Subgroup D) (hP : IsPGroup 5 P) : P ≤ pResidual 2 D := by
  intro x hx
  apply mem_pResidual_of_orderOf_coprime
  rw [Subgroup.orderOf_coe (⟨x,hx⟩ : P)]
  exact (hP.orderOf_coprime (by decide : Nat.Coprime 5 2) _).symm

include s in
private theorem sylow_five_image_eq_residual (P : Sylow 5 H) :
    (P : Subgroup H).map (QuotientGroup.mk' (pCore 2 H)) = pResidual 2 (H ⧸ pCore 2 H) := by
  let := s.primitive.elementary
  let R := P.mapSurjective (f := QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  apply le_antisymm
  · exact five_subgroup_le_residual _ R.isPGroup'
  · exact (IsElementaryAbelian.isPGroup 5 _).le_sylow_of_normal R

include s in
private theorem source_component_sylow_intersections_split
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T))
    (P : Sylow 5 Mc) :
    (P : Subgroup Mc) ⊓ (residualClosure H Mc).subgroupOf Mc =
      ((P : Subgroup Mc) ⊓ b.K1.subgroupOf Mc) ⊔
      ((P : Subgroup Mc) ⊓ b.K2.subgroupOf Mc) := by
  let KM := (residualClosure H Mc).subgroupOf Mc
  let K1M := b.K1.subgroupOf Mc
  let K2M := b.K2.subgroupOf Mc
  have hn := source_exchanged_closure_normalizes_factors s b
  have h1 : b.K1 ≤ residualClosure H Mc :=
    (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ residualClosure H Mc :=
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

include s in
theorem source_exchanged_actor_join
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    actorImage H b.K1 ⊔ actorImage H b.K2 = pResidual 2 (H ⧸ pCore 2 H) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hA (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
      (em : Nonempty ((K ⧸ pCore 2 K) ≃* Theory.PSL2.SixteenWreathComponents.L))
      (hKz : K ≤ residualClosure H Mc) : actorImage H K ≤ pResidual 2 (H ⧸ pCore 2 H) := by
    apply five_subgroup_le_residual
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one] using source_exchanged_component_actor_card s b hKM hK em hKz
  have h1 : b.K1 ≤ residualClosure H Mc :=
    (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ residualClosure H Mc :=
    (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  apply le_antisymm (sup_le (hA _ b.first_le b.first_component b.first_model h1)
    (hA _ b.second_le b.second_component b.second_model h2))
  let P : Sylow 5 H := Classical.choice inferInstance
  let eH := subgroupOfEquivOfLe (original_H_le_partner s)
  let P0 := P.mapSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  let PM : Sylow 5 Mc := P0.mapSubtypeOfIndexPrimeTo (source_exchanged_outside_index_primeTo_five s)
  have he : (PM : Subgroup Mc).map Mc.subtype = (P : Subgroup H).map H.subtype := by
    change (((P : Subgroup H).map eH.symm.toMonoidHom).map (H.subgroupOf Mc).subtype).map
      Mc.subtype = _
    rw [map_map,map_map]
    rfl
  have hPK : (PM : Subgroup Mc) ≤ (residualClosure H Mc).subgroupOf Mc := by
    intro x hx
    have hh : (x : G) ∈ (P : Subgroup H).map H.subtype := he ▸ mem_map_of_mem Mc.subtype hx
    obtain ⟨y,hy,hyx⟩ := hh
    have hr : (y : G) ∈ residual H := mem_map_of_mem H.subtype
      (five_subgroup_le_residual _ P.isPGroup' hy)
    change (x : G) ∈ residualClosure H Mc
    rw [←hyx]
    exact le_conjugateSpanBy (residual H) Mc hr
  have hs := source_component_sylow_intersections_split s b PM
  rw [inf_eq_left.mpr hPK] at hs
  have hgen := congrArg (map Mc.subtype) hs
  rw [he,Subgroup.map_sup,Subgroup.map_inf _ _ _ Mc.subtype_injective,
    Subgroup.map_inf _ _ _ Mc.subtype_injective,he,
    map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] at hgen
  let J := actorImage H b.K1 ⊔ actorImage H b.K2
  let C := (J.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype
  have hf (K : Subgroup G) (hK : actorImage H K ≤ J) :
      ((P : Subgroup H).map H.subtype) ⊓ K ≤ C := by
    rintro x ⟨⟨y,hy,hyx⟩,hxK⟩
    refine ⟨y,?_,hyx⟩
    have hyK : y ∈ K.subgroupOf H := by
      change H.subtype y ∈ K
      rw [hyx]
      exact hxK
    exact hK (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hyK)
  have hPC : (P : Subgroup H).map H.subtype ≤ C := by
    rw [hgen]
    exact sup_le (hf _ le_sup_left) (hf _ le_sup_right)
  rw [←sylow_five_image_eq_residual s P]
  apply map_le_iff_le_comap.mpr
  intro x hx
  have hh := hPC (mem_map_of_mem H.subtype hx)
  exact (mem_map_iff_mem H.subtype_injective).mp hh

include s in
theorem source_exchanged_actor_disjoint
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    Disjoint (actorImage H b.K1) (actorImage H b.K2) := by
  let A := actorImage H b.K1
  let B := actorImage H b.K2
  have h1 : b.K1 ≤ residualClosure H Mc :=
    (le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have h2 : b.K2 ≤ residualClosure H Mc :=
    (le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq
  have hA : Nat.card A = 5 :=
    source_exchanged_component_actor_card s b b.first_le b.first_component b.first_model h1
  have hB : Nat.card B = 5 :=
    source_exchanged_component_actor_card s b b.second_le b.second_component b.second_model h2
  have hd : Nat.card (A ⊓ B : Subgroup (H ⧸ pCore 2 H)) ∣ 5 :=
    hA ▸ card_dvd_of_le (show A ⊓ B ≤ A from inf_le_left)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with hc | hc
  · exact disjoint_iff.mpr (card_eq_one.mp hc)
  · have heA : A ⊓ B = A := eq_of_le_of_card_ge inf_le_left (by rw [hc,hA])
    have heB : A ⊓ B = B := eq_of_le_of_card_ge inf_le_right (by rw [hc,hB])
    have hj : A ⊔ B = pResidual 2 (H ⧸ pCore 2 H) := source_exchanged_actor_join s b
    rw [←heB,heA,sup_idem] at hj
    have h25 := s.factors.residual_card
    rw [←hj,hA] at h25
    norm_num at h25

include s in
theorem source_exchanged_actor_product
    (b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T)) :
    ∃ e : actorImage H b.K1 × actorImage H b.K2 ≃* pResidual 2 (H ⧸ pCore 2 H),
      ∀ x y, (e (x,y) : H ⧸ pCore 2 H) = (x : H ⧸ pCore 2 H) * (y : H ⧸ pCore 2 H) := by
  let := s.primitive.elementary
  have hj := source_exchanged_actor_join s b
  have h1 : actorImage H b.K1 ≤ pResidual 2 (H ⧸ pCore 2 H) :=
    (le_sup_left : actorImage H b.K1 ≤ actorImage H b.K1 ⊔ actorImage H b.K2).trans_eq hj
  have h2 : actorImage H b.K2 ≤ pResidual 2 (H ⧸ pCore 2 H) :=
    (le_sup_right : actorImage H b.K2 ≤ actorImage H b.K1 ⊔ actorImage H b.K2).trans_eq hj
  have hc : actorImage H b.K1 ≤ centralizer (actorImage H b.K2 : Set (H ⧸ pCore 2 H)) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨y,h2 hy⟩ : pResidual 2 (H ⧸ pCore 2 H)) ⟨x,h1 hx⟩)
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage H b.K1) (actorImage H b.K2) (source_exchanged_actor_disjoint s b) hc
  exact ⟨e.trans (MulEquiv.subgroupCongr hj),he⟩

include s in
theorem source_exchanged_actor_decomposition :
    ∃ b : ExchangedFactorData (T : Subgroup G) Mc H (centralInvolutions T),
      Nat.card (actorImage H b.K1) = 5 ∧ Nat.card (actorImage H b.K2) = 5 ∧
      Disjoint (actorImage H b.K1) (actorImage H b.K2) ∧
      ∃ e : actorImage H b.K1 × actorImage H b.K2 ≃* pResidual 2 (H ⧸ pCore 2 H),
        ∀ x y, (e (x,y) : H ⧸ pCore 2 H) = (x : H ⧸ pCore 2 H) * (y : H ⧸ pCore 2 H) := by
  obtain ⟨b,h1,h2⟩ := source_exchanged_actor_cardinalities s
  exact ⟨b,h1,h2,source_exchanged_actor_disjoint s b,source_exchanged_actor_product s b⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
