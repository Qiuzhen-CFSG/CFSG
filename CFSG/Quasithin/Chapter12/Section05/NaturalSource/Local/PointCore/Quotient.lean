module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Seven
public import Theory.ElementaryAbelian.EightQuotientRank
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.GroupTheory.SubgroupTransport
public import Theory.ElementaryAbelian.Injective

/-!
# The two literal quotients in the point-core argument

Write U₁ for the G₁-normal closure of V₇. Its reduced image in G₁/V₁
centralizes the image of O₂(G₁), so [U₁,O₂(G₁)] ≤ V₁. Consequently
U₁/V₁ is elementary abelian and the original conjugation action factors
through G₁/O₂(G₁), with its formula on representatives preserved.

If V is not contained in O₂(G₁), the previously proved intersection
V ∩ O₂(G₁) = V₇ gives an image of order eight. Its commutator with the
original L₁ image is the entire image. These are quotient inputs to the
remaining large-model cases, rather than an assertion of their exclusion.
The local owner constructs those exclusions and qt-d-1251-source assembles
the final exterior theorem.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.SL5ExteriorSquare
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- Reducedness centralizes the point core modulo the original point. -/
theorem sevenClosure_commutator_point_core_le_point
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ⁅s.sevenClosure, (s.marking.Gi 1).pCoreIn 2⁆ ≤ s.marking.Vi 1 := by
  let H := s.marking.Gi 1
  let N := (s.marking.Vi 1).subgroupOf H
  have h1H : s.marking.Vi 1 ≤ H := (s.marking.Vi 1).le_normalizer
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer h1H).mpr le_rfl
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hr := s.sevenClosure_image_reduced h q (QuotientGroup.mk'_surjective N)
    (QuotientGroup.ker_mk' N)
  have hmap : (pCore 2 H).map q ≤ pCore 2 (H ⧸ N) :=
    le_sSup ⟨Normal.map inferInstance q (QuotientGroup.mk'_surjective N),
      pCore_isPGroup.map q⟩
  have hz : ⁅(s.sevenClosure.subgroupOf H).map q, (pCore 2 H).map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hr.le_centralizer_pCore.trans (centralizer_le hmap))
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hz
  have hi : ⁅s.sevenClosure, H.pCoreIn 2⁆ ≤ H :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le
      ((s.sevenClosure_le_point_core h).trans (pCoreIn_le 2 H)) (pCoreIn_le 2 H))
  have hcore : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have he := SubgroupTransport.subgroupOf_commutator s.sevenClosure (H.pCoreIn 2)
    ((s.sevenClosure_le_point_core h).trans (pCoreIn_le 2 H)) (pCoreIn_le 2 H)
  rw [hcore] at he
  rw [← he] at hz
  change ⁅s.sevenClosure, H.pCoreIn 2⁆.subgroupOf H ≤ (s.marking.Vi 1).subgroupOf H at hz
  have hh := map_mono (f := H.subtype) hz
  simpa only [map_subgroupOf_eq_of_le hi, map_subgroupOf_eq_of_le h1H] using hh

omit [Finite G] in
/-- The original seven-space has the cardinality of its marked coordinates. -/
theorem card_V₇ : Nat.card (s.marking.Vi 7) = 128 := by
  have he : Nat.card (s.marking.subspace V₇) = Nat.card V₇ := by
    apply Nat.card_congr
    exact {
      toFun x := ⟨(s.marking.coordinates ⟨x, s.marking.subspace_le V₇ x.property⟩).toAdd,
        (s.marking.mem_subspace V₇ _).mp x.property⟩
      invFun x := ⟨(s.marking.coordinates.symm (Multiplicative.ofAdd x.val) : V),
        (s.marking.mem_subspace V₇ _).mpr
          (by rw [MulEquiv.apply_symm_apply]; exact x.property)⟩
      left_inv x := by
        apply Subtype.ext
        change (s.marking.coordinates.symm (s.marking.coordinates
          ⟨x, s.marking.subspace_le V₇ x.property⟩) : G) = x
        exact congrArg (fun v : V => (v : G)) (s.marking.coordinates.symm_apply_apply _)
      right_inv x := by
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (s.marking.coordinates.apply_symm_apply _) }
  change Nat.card (s.marking.subspace V₇) = 128
  rw [he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    standard_dimensions.2.2.2.2.1]
  norm_num

/-- Failure of point-core containment leaves the original three-dimensional image. -/
theorem seed_core_image_card_of_failure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2)
    {Q : Type*} [Group Q] (q : s.marking.Gi 1 →* Q)
    (hker : q.ker = pCore 2 (s.marking.Gi 1)) :
    Nat.card ((V.subgroupOf (s.marking.Gi 1)).map q) = 8 := by
  let H := s.marking.Gi 1
  have hVH : V ≤ H := D.le_sylow.trans s.sylow_le_G₁
  have h7H : s.marking.Vi 7 ≤ H := (s.marking.subspace_le _).trans hVH
  have hi : V.subgroupOf H ⊓ q.ker = (s.marking.Vi 7).subgroupOf H := by
    rw [hker, ← comap_map_eq_self_of_injective H.subtype_injective (pCore 2 H)]
    change (V ⊓ H.pCoreIn 2).subgroupOf H = _
    rw [s.seed_inf_point_core_of_failure h hfail]
  have hV : Nat.card V = 1024 := by
    rw [Nat.card_congr s.marking.coordinates.toEquiv,
      Nat.card_congr Multiplicative.toAdd,
      Nat.card_congr Representation.SL5ExteriorSquare.coordinates.toEquiv]
    norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hc := IsElementaryAbelian.card_inf_ker_mul_card_map (V.subgroupOf H) q
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe h7H).toEquiv, s.card_V₇,
    Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv, hV] at hc
  change Nat.card ((V.subgroupOf H).map q) = 8
  omega

/-- The original residual fully moves the seed image under every quotient map. -/
theorem seed_core_image_fully_moved {Q : Type*} [Group Q]
    (q : s.marking.Gi 1 →* Q) :
    ⁅(V.subgroupOf (s.marking.Gi 1)).map q,
      ((s.marking.Li 1).subgroupOf (s.marking.Gi 1)).map q⁆ =
      (V.subgroupOf (s.marking.Gi 1)).map q := by
  rw [← map_commutator, ← SubgroupTransport.subgroupOf_commutator V (s.marking.Li 1)
    (D.le_sylow.trans s.sylow_le_G₁) (s.marking.Li_le_Gi 1), s.seed_point_commutator]

omit [Finite G] in
/-- The source point is normal in its seven-space normal closure. -/
theorem point_normal_in_sevenClosure :
    ((s.marking.Vi 1).subgroupOf s.sevenClosure).Normal := by
  have h1U := s.V₁_lt_V₇.le.trans s.seven_le_sevenClosure
  apply (normal_subgroupOf_iff_le_normalizer h1U).mpr
  exact map_subtype_le _

/-- The literal quotient U₁/V₁ inherits the elementary reduced image. -/
theorem sevenClosure_quotient_elementary
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let := s.point_normal_in_sevenClosure
    IsElementaryAbelian 2 (s.sevenClosure ⧸ (s.marking.Vi 1).subgroupOf s.sevenClosure) := by
  let := s.point_normal_in_sevenClosure
  let H := s.marking.Gi 1
  let U := s.sevenClosure
  let N := (s.marking.Vi 1).subgroupOf H
  have hUH : U ≤ H := map_subtype_le _
  have h1H : s.marking.Vi 1 ≤ H := (s.marking.Vi 1).le_normalizer
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer h1H).mpr le_rfl
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  let W := (U.subgroupOf H).map q
  have hr := s.sevenClosure_image_reduced h q (QuotientGroup.mk'_surjective N)
    (QuotientGroup.ker_mk' N)
  let : IsElementaryAbelian 2 W := hr.elementary
  let f : U →* W := (q.subgroupMap (U.subgroupOf H)).comp
    (subgroupOfEquivOfLe hUH).symm.toMonoidHom
  have hf : Function.Surjective f :=
    (q.subgroupMap_surjective _).comp (subgroupOfEquivOfLe hUH).symm.surjective
  have hk : f.ker = (s.marking.Vi 1).subgroupOf U := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change q ⟨(x : G), hUH x.property⟩ = 1 ↔ (x : G) ∈ s.marking.Vi 1
    exact QuotientGroup.eq_one_iff _
  let e := QuotientGroup.liftEquiv ((s.marking.Vi 1).subgroupOf U) hf hk.symm
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

/-- The original action on U₁/V₁ descends through the full point core. -/
theorem exists_point_core_quotient_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let := s.point_normal_in_sevenClosure
    ∃ ρ : (s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1)) →*
        MulAut (s.sevenClosure ⧸ (s.marking.Vi 1).subgroupOf s.sevenClosure),
      ∀ (g : s.marking.Gi 1) (u : s.sevenClosure),
        ρ (QuotientGroup.mk' (pCore 2 (s.marking.Gi 1)) g)
          (QuotientGroup.mk' ((s.marking.Vi 1).subgroupOf s.sevenClosure) u) =
        QuotientGroup.mk' ((s.marking.Vi 1).subgroupOf s.sevenClosure)
          ⟨(g : G) * (u : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (s.point_normalizes_sevenClosure g.property) u).mp u.property⟩ := by
  let := s.point_normal_in_sevenClosure
  let H := s.marking.Gi 1
  obtain ⟨ρ, hρ⟩ := exists_quotient_conjugation_action H s.sevenClosure
    (s.marking.Vi 1) s.point_normalizes_sevenClosure le_rfl s.point_normal_in_sevenClosure
  have hk := quotient_conjugation_action_kills_commutator_layer H s.sevenClosure
    (s.marking.Vi 1) (H.pCoreIn 2) s.point_normal_in_sevenClosure
    s.point_normalizes_sevenClosure (s.sevenClosure_commutator_point_core_le_point h) ρ hρ
  have hc : pCore 2 H ≤ ρ.ker := by
    simpa only [pCoreIn, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective] using hk
  exact ⟨QuotientGroup.lift (pCore 2 H) ρ hc, hρ⟩

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
