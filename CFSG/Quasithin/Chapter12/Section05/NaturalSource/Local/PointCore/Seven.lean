module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Chief
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.Membership
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.GroupTheory.PCoreSurjective

/-!
# The seven-space closure in the point centralizer

The actual point quotient G₁/V₁ has the nonzero irreducible seed V₇/V₁.
The original Sylow lies in its normalizer, and Hypothesis 12.2.3 makes G₁
characteristic two. The G.2.2 irreducible-closure theorem therefore makes
its normal closure reduced. Its containment in the quotient two-core lifts
through the elementary kernel, giving V₇ ≤ O₂(G₁).

The embedded G₁-normal closure U₁ of V₇ also lies in that core. If V is
not contained in O₂(G₁), irreducibility of V/V₇ gives V ∩ O₂(G₁) = V₇, hence
V ∩ U₁ = V₇ and [V,U₁] ≤ V₇. These are the literal subgroup and quotient
inputs to the remaining large-model exclusions, which stay with this local
owner. The final exterior exclusion is owned by qt-d-1251-source.

Source: Aschbacher--Smith, proof of 12.5.8(1), printed p.820, using G.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.SL5ExteriorSquare
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

theorem V₁_lt_V₇ : s.marking.Vi 1 < s.marking.Vi 7 := by
  refine lt_of_le_of_ne (s.marking.subspace_mono standard_chief_chain_strict.2.1.le) ?_
  intro he
  exact standard_chief_chain_strict.2.1.ne (s.marking.subspace_injective he)

theorem point_component_normalizes_seven :
    L ⊓ s.marking.Gi 1 ≤ normalizer (s.marking.Vi 7 : Set G) := by
  intro l hl
  exact (s.marking.mem_normalizer_subspace V₇ ⟨l, hl.1⟩).mpr
    (parabolic_two_le_stabilizer_V₇
      ((s.marking.mem_Gi_iff_actor 1 (Or.inl rfl) ⟨l, hl.1⟩).mp hl.2))

/-- The original G₁-normal closure of V₇, embedded back in G. -/
@[expose] def sevenClosure : Subgroup G :=
  (normalClosure ((s.marking.Vi 7).subgroupOf (s.marking.Gi 1) :
    Set (s.marking.Gi 1))).map (s.marking.Gi 1).subtype

theorem seven_le_sevenClosure : s.marking.Vi 7 ≤ s.sevenClosure := by
  intro v hv
  have hvH : v ∈ s.marking.Gi 1 := s.sylow_le_G₁ (D.le_sylow (s.marking.subspace_le _ hv))
  exact ⟨⟨v, hvH⟩, le_normalClosure hv, rfl⟩

theorem point_normalizes_sevenClosure :
    s.marking.Gi 1 ≤ normalizer (s.sevenClosure : Set G) := by
  simpa only [sevenClosure, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
    using (normalClosure ((s.marking.Vi 7).subgroupOf (s.marking.Gi 1) :
      Set (s.marking.Gi 1))).le_normalizer_map (s.marking.Gi 1).subtype

variable [Finite G]

/-- G.2.2 for the actual point quotient, expressed through any surjection with
its exact kernel. Its normal closure uses the original marked seven-space. -/
theorem seven_closure_image_reduced (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {Q : Type*} [Group Q] [Finite Q]
    (q : s.marking.Gi 1 →* Q) (hq : Function.Surjective q)
    (hker : q.ker = (s.marking.Vi 1).subgroupOf (s.marking.Gi 1)) :
    IsPReduced 2 (normalClosure
      (((s.marking.Vi 7).subgroupOf (s.marking.Gi 1)).map q : Set Q)) := by
  let H := s.marking.Gi 1
  let A := (L ⊓ H) ⊔ (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := s.sylow_le_G₁
  have h7T : s.marking.Vi 7 ≤ (T : Subgroup G) :=
    (s.marking.subspace_le _).trans D.le_sylow
  have h7H := h7T.trans hTH
  have h1H : s.marking.Vi 1 ≤ H := (s.marking.Vi 1).le_normalizer
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) (s.marking.Gi_twoLocal 1 (Or.inl rfl)) hTH)
  let := D.elementary
  let : IsElementaryAbelian 2 (s.marking.Vi 7) := IsElementaryAbelian.of_le (s.marking.subspace_le _)
  let : IsElementaryAbelian 2 ((s.marking.Vi 7).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf h7H
  have hNV : q.ker ≤ (s.marking.Vi 7).subgroupOf H := by
    rw [hker]
    exact comap_mono s.V₁_lt_V₇.le
  have hne : q.ker ≠ (s.marking.Vi 7).subgroupOf H := by
    rw [hker]
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le h1H, map_subgroupOf_eq_of_le h7H] at hh
    exact s.V₁_lt_V₇.ne hh
  have hAn : A ≤ normalizer (s.marking.Vi 7 : Set G) :=
    sup_le s.point_component_normalizes_seven
      (s.sylow_normalizes_subspace V₇ flagGroup_stabilizes_standard.2.2.2.2)
  have hnorm : A.subgroupOf H ≤ normalizer ((s.marking.Vi 7).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq h7H]
    exact comap_mono hAn
  have hirr : ∀ E : Subgroup H, q.ker ≤ E → E ≤ (s.marking.Vi 7).subgroupOf H →
      A.subgroupOf H ≤ normalizer (E : Set H) →
      E = q.ker ∨ E = (s.marking.Vi 7).subgroupOf H := by
    intro E hNE hE7 hn
    have h1E : s.marking.Vi 1 ≤ E.map H.subtype := by
      rw [← map_subgroupOf_eq_of_le h1H]
      apply map_mono
      rwa [← hker]
    have hE7' : E.map H.subtype ≤ s.marking.Vi 7 := by
      simpa only [map_subgroupOf_eq_of_le h7H] using map_mono (f := H.subtype) hE7
    have hnE : L ⊓ H ≤ normalizer (E.map H.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro l hl _ ⟨v, hv, rfl⟩
      refine ⟨⟨l, hl.2⟩ * v * ⟨l, hl.2⟩⁻¹, ?_, rfl⟩
      exact le_normalizer_iff.mp hn ⟨l, hl.2⟩ ((show L ⊓ H ≤ A from le_sup_left) hl) v hv
    rcases s.marking.point_middle_invariant_interval_of_component
      (E.map H.subtype) h1E hE7' hnE with he | he
    · left
      apply map_injective H.subtype_injective
      rw [he, hker, map_subgroupOf_eq_of_le h1H]
    · right
      apply map_injective H.subtype_injective
      rw [he, map_subgroupOf_eq_of_le h7H]
  exact isPReduced_normalClosure_image_of_irreducible q
    hq ((s.marking.Vi 7).subgroupOf H)
    (A.subgroupOf H) (T.subtype hTH) hchar inferInstance hNV hne
    (by intro v hv; exact h7T hv)
    (by intro v hv; exact (show (T : Subgroup G) ≤ A from le_sup_right) hv)
    hnorm hirr

/-- The preceding reducedness statement on the literal image of U₁. -/
theorem sevenClosure_image_reduced (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {Q : Type*} [Group Q] [Finite Q]
    (q : s.marking.Gi 1 →* Q) (hq : Function.Surjective q)
    (hker : q.ker = (s.marking.Vi 1).subgroupOf (s.marking.Gi 1)) :
    IsPReduced 2 ((s.sevenClosure.subgroupOf (s.marking.Gi 1)).map q) := by
  have he : s.sevenClosure.subgroupOf (s.marking.Gi 1) =
      normalClosure ((s.marking.Vi 7).subgroupOf (s.marking.Gi 1) : Set (s.marking.Gi 1)) :=
    comap_map_eq_self_of_injective (s.marking.Gi 1).subtype_injective _
  rw [he, map_normalClosure _ q hq]
  exact s.seven_closure_image_reduced h q hq hker

/-- The preliminary point-core containment in source 12.5.8(1). -/
theorem seven_le_point_core (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.marking.Vi 7 ≤ (s.marking.Gi 1).pCoreIn 2 := by
  let H := s.marking.Gi 1
  let N := (s.marking.Vi 1).subgroupOf H
  have h1H : s.marking.Vi 1 ≤ H := (s.marking.Vi 1).le_normalizer
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer h1H).mpr le_rfl
  let q : H →* H ⧸ N := QuotientGroup.mk' N
  have hker : q.ker = N := QuotientGroup.ker_mk' N
  have hr := s.seven_closure_image_reduced h q (QuotientGroup.mk'_surjective N) hker
  let := D.elementary
  have h7H : s.marking.Vi 7 ≤ H :=
    ((s.marking.subspace_le _).trans D.le_sylow).trans s.sylow_le_G₁
  have hi : ((s.marking.Vi 7).subgroupOf H).map q ≤ pCore 2 (H ⧸ N) :=
    le_normalClosure.trans hr.le_pCore
  have hk : IsPGroup 2 q.ker := by
    rw [hker]
    let : IsElementaryAbelian 2 (s.marking.Vi 1) :=
      IsElementaryAbelian.of_le (s.marking.subspace_le _)
    exact (IsElementaryAbelian.isPGroup 2 (s.marking.Vi 1)).comap_subtype
  have hc := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective N) hk
  have h7core : (s.marking.Vi 7).subgroupOf H ≤ pCore 2 H := by
    rw [← hc]
    exact map_le_iff_le_comap.mp hi
  intro v hv
  exact ⟨⟨v, h7H hv⟩, h7core hv, rfl⟩

theorem sevenClosure_le_point_core (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    s.sevenClosure ≤ (s.marking.Gi 1).pCoreIn 2 := by
  let H := s.marking.Gi 1
  have hs : (s.marking.Vi 7).subgroupOf H ≤ pCore 2 H := by
    have hh := comap_mono (f := H.subtype) (s.seven_le_point_core h)
    change (s.marking.Vi 7).subgroupOf H ≤ ((pCore 2 H).map H.subtype).comap H.subtype at hh
    rwa [comap_map_eq_self_of_injective H.subtype_injective] at hh
  exact map_mono (normalClosure_le_normal hs)

theorem seed_inf_point_core_of_failure (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    V ⊓ (s.marking.Gi 1).pCoreIn 2 = s.marking.Vi 7 := by
  let H := s.marking.Gi 1
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hn : L ⊓ H ≤ normalizer (V ⊓ H.pCoreIn 2 : Set G) :=
    (le_inf (inf_le_left.trans D.normalizes) (inf_le_right.trans hnQ)).trans
      inf_normalizer_le_normalizer_inf
  rcases s.marking.point_upper_invariant_interval_of_component
    (V ⊓ H.pCoreIn 2) (le_inf (s.marking.subspace_le _) (s.seven_le_point_core h))
    inf_le_left hn with he | he
  · exact he
  · exact (hfail (he.symm.le.trans inf_le_right)).elim

theorem seed_inf_sevenClosure_of_failure (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    V ⊓ s.sevenClosure = s.marking.Vi 7 := by
  apply le_antisymm
  · exact (inf_le_inf_left V (s.sevenClosure_le_point_core h)).trans
      (s.seed_inf_point_core_of_failure h hfail).le
  · exact le_inf (s.marking.subspace_le _) s.seven_le_sevenClosure

theorem seed_commutator_sevenClosure_le_seven
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hfail : ¬ V ≤ (s.marking.Gi 1).pCoreIn 2) :
    ⁅V, s.sevenClosure⁆ ≤ s.marking.Vi 7 := by
  have hQT : (s.marking.Gi 1).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (s.marking.Gi 1) (T.subtype s.sylow_le_G₁)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le s.sylow_le_G₁] using hh
  have hnV : s.sevenClosure ≤ normalizer (V : Set G) :=
    ((s.sevenClosure_le_point_core h).trans hQT).trans
      ((show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right).trans s.normalizes)
  have hnU : V ≤ normalizer (s.sevenClosure : Set G) :=
    (D.le_sylow.trans s.sylow_le_G₁).trans s.point_normalizes_sevenClosure
  rw [← s.seed_inf_sevenClosure_of_failure h hfail]
  apply le_inf
  · rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp hnV
  · exact le_normalizer_iff_commutator_le_right.mp hnU

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
