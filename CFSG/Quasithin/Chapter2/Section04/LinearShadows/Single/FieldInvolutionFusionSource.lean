module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CyclicSource
public import Theory.GroupTheory.ElementaryLayerInvolutionFusion
public import Theory.ElementaryAbelian.Quotient

/-!
# The two elementary layers in the original involution-fusion argument

The actual core Q=O₂(H) is normal and elementary in R=J(S). The conjugate
maximum elementary subgroup generates R modulo Q, so R/Q is elementary too.
Every actor in S preserves these layers. Consequently square-root fixed-point
counts on these two literal actions give R-fusion of all involutions in sR.

The two fixed-point counts remain explicit: they are the natural-module and
field-action calculations in Aschbacher–Smith, Lemma 2.4.12(2), printed p.532.
This module discharges the group-theoretic Exercise 2.8 step and every layer
and normalization premise for the original 2.4.21 consumer.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
theorem source_field_core_normal (d : MinimalBlockSetup M) :
    ((twoCore d.H).subgroupOf
      (Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  have hRS : Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype) ≤
      (d.S : Subgroup d.H).map d.H.subtype := sSup_le fun _ h => h.1
  exact hRS.trans ((map_subtype_le _).trans
    (d.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H))))

omit [Finite G] in
theorem source_field_actor_normalizes_thompson (d : MinimalBlockSetup M)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype) :
    s ∈ normalizer (Stellmacher.elementaryAbelianMaxJ
      ((d.S : Subgroup d.H).map d.H.subtype) : Set G) :=
  ((d.S : Subgroup d.H).map d.H.subtype).le_normalizer.trans
    (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ _) hs

omit [Finite G] in
theorem source_field_actor_preserves_core (d : MinimalBlockSetup M)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    ∀ x ∈ N, R.normalizerMonoidHom
      ⟨s,source_field_actor_normalizes_thompson d s hs⟩ x ∈ N := by
  intro R N x hx
  change s * x.val * s⁻¹ ∈ twoCore d.H
  have hn : s ∈ normalizer (twoCore d.H : Set G) :=
    (d.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H)))
      (map_subtype_le _ hs)
  exact (mem_normalizer_iff.mp hn x.val).mp hx

theorem source_field_elementary_layers
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    IsElementaryAbelian 2 N ∧ IsElementaryAbelian 2 (R ⧸ N) := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let Q := twoCore d.H
  let N := Q.subgroupOf R
  let : N.Normal := source_field_core_normal d
  change IsElementaryAbelian 2 N ∧ IsElementaryAbelian 2 (R ⧸ N)
  have hQR : Q ≤ R := le_sSup (d.core_source hG T hST).2.2
  let : IsElementaryAbelian 2 Q := (d.core_source hG T hST).2.2.2.1
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.subgroupOf hQR
  refine ⟨inferInstance,?_⟩
  obtain ⟨x,hxT,hxS,_⟩ := c.outside
  let V := Q.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hpair : R = Q ⊔ V := by
    have hh := (source_absorbed_sylow_family d hG T hST hsingle hL hM hTM hunique).2.2.2 x hxT hxS
    simpa only [(lemma_2_4_8_2 d hG T hST hsingle hL hM hTM hunique).2] using hh.1
  have hVR : V ≤ R := le_sup_right.trans_eq hpair.symm
  let : IsElementaryAbelian 2 (V.subgroupOf R) := IsElementaryAbelian.subgroupOf hVR
  let φ : V.subgroupOf R →* R ⧸ N := (QuotientGroup.mk' N).comp (V.subgroupOf R).subtype
  apply IsElementaryAbelian.of_surjective φ
  intro a
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective N a
  have hr : r ∈ N ⊔ V.subgroupOf R := by
    rw [←subgroupOf_sup hQR hVR,←hpair,subgroupOf_self]
    exact mem_top r
  obtain ⟨u,hu,v,hv,he⟩ := mem_sup_of_normal_left.mp hr
  refine ⟨⟨v,hv⟩,?_⟩
  change QuotientGroup.mk' N v = QuotientGroup.mk' N r
  have huq : QuotientGroup.mk' N u = 1 := (QuotientGroup.eq_one_iff u).mpr hu
  rw [←he,map_mul,huq,one_mul]

theorem source_field_involution_coset_fusion_of_fixed_cards
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let N := (twoCore d.H).subgroupOf R
    let : N.Normal := source_field_core_normal d
    let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
    let hN := source_field_actor_preserves_core d s hs.1
    Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N →
    Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N) →
    ∀ v ∈ T, orderOf v = 2 → v * s⁻¹ ∈ R → ∃ r ∈ R, r * s * r⁻¹ = v := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
  let N := (twoCore d.H).subgroupOf R
  let : N.Normal := source_field_core_normal d
  let α := (R.normalizerMonoidHom ⟨s,source_field_actor_normalizes_thompson d s hs.1⟩).toMonoidHom
  let hN := source_field_actor_preserves_core d s hs.1
  change Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N →
    Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N) → _
  intro hcN hcQ v _ hv hvR
  have he := source_field_elementary_layers d hG T hST hsingle hL hM hTM hunique c
  let : IsElementaryAbelian 2 N := he.1
  let : IsElementaryAbelian 2 (R ⧸ N) := he.2
  exact Theory.GroupTheory.involution_coset_fusion_of_elementary_layers R N s
    (by simpa only [hs2] using pow_orderOf_eq_one s)
    (source_field_actor_normalizes_thompson d s hs.1) hN hcN hcQ v
    (by simpa only [hv] using pow_orderOf_eq_one v) hvR
end CFSG.Quasithin.Chapter2.LinearShadows.Single
