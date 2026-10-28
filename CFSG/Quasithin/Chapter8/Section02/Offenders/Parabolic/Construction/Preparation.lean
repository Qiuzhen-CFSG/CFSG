module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Family
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Elementary
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.Geometry
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Local hypotheses for the selected pair

Source: Aschbacher–Smith, Proposition 8.2.2, printed pp.714–715; B.6.8(5),
E.2.8, E.2.13(6), and E.2.14(7).

A two-subgroup of a normal two-closed subgroup lies in the ambient two-core.
Thus B.6.8(5) converts the independent V not ≤ O₂(H) input into E.2.8's
noncontainment in the literal core. The positive weak-closure parameter
supplies E.2.13(6)'s commuting-conjugate hypothesis inside the selected I.
Restriction to the induced automizer of M ∩ I preserves the lower quadratic
ratio bound: injective restriction preserves the actor rank and fixed space.

The classified existence theorem and E.2 module refinements remain earlier
source inputs. None of the following lemmas asserts the complete 8.2.2.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE ChapterB
variable {G : Type*} [Group G]

/-- The elementary consequence of two-closedness used with B.6.8(5). -/
private theorem two_subgroup_le_core_of_normal_two_closed [Finite G]
    (N V : Subgroup G) [N.Normal] (hN : IsTwoClosed N)
    (hV : IsPGroup 2 V) (hVN : V ≤ N) : V ≤ pCore 2 G := by
  obtain ⟨S, hS⟩ := hN
  let := Sylow.unique_of_normal S hS
  have hp : IsPGroup 2 (V.subgroupOf N) := hV.comap_subtype
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  have hVS : V.subgroupOf N ≤ (S : Subgroup N) := by
    simpa only [Subsingleton.elim R S] using hR
  have hSc : (S : Subgroup N) ≤ pCore 2 N := le_sSup ⟨hS, S.isPGroup'⟩
  have hmap := map_mono (f := N.subtype) (hVS.trans hSc)
  rw [map_subgroupOf_eq_of_le hVN] at hmap
  exact hmap.trans (le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
    pCore_isPGroup.map N.subtype⟩)

/-- The noncontainment required by E.2.8, with both normal cores intrinsic
to H and then embedded into the original group. -/
theorem outside_localCore [Finite G] (H M V : Subgroup G)
    (hV : IsPGroup 2 V) (hVH : V ≤ H)
    (hclosed : IsTwoClosed (localCore M H))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype) :
    ¬ V ≤ (localCore M H).map H.subtype := by
  intro hc
  have hlocal : V.subgroupOf H ≤ localCore M H := by
    have hm := comap_mono (f := H.subtype) hc
    rwa [comap_map_eq_self_of_injective H.subtype_injective] at hm
  have hq := two_subgroup_le_core_of_normal_two_closed (localCore M H)
    (V.subgroupOf H) hclosed hV.comap_subtype hlocal
  have hm := map_mono (f := H.subtype) hq
  rw [map_subgroupOf_eq_of_le hVH] at hm
  exact hout hm

/-- Apply the B.6.8(5) input to obtain the exact E.2.8 setup. The additional
standing data are the actual minimal parabolic, SQTK and local two-core data. -/
theorem hypothesisE28_of_outside_twoCore [Finite G] (K : GroupClass)
    (H T M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hTH : T ≤ H) (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hP : IsMinimalParabolicOver S ⊤)
    (hM : M.subgroupOf H = minimalParabolicMax S hP)
    (hK : IsSQTK K H) (hVT : V ≤ T) (hn : (V.subgroupOf T).Normal)
    (hVM : V ≤ (pCore 2 (M.subgroupOf H)).map
      (H.subtype.comp (M.subgroupOf H).subtype))
    (hclosed : IsTwoClosed (localCore M H))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype) : HypothesisE28 K H T M V := by
  exact ⟨hTH, ⟨S, hS, hP, hM⟩, hK, inferInstance, hVT, hn, hVM,
    outside_localCore H M V (IsElementaryAbelian.isPGroup 2 V)
      (hVT.trans hTH) hclosed hout⟩

/-- Restriction to I commutes with the source's right conjugation. -/
theorem restricted_right_conjugate_image (I V : Subgroup G) (hVI : V ≤ I) (i : I) :
    ((V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom).map I.subtype =
      V.map (MulAut.conj (i.val)⁻¹).toMonoidHom := by
  have hc : I.subtype.comp (MulAut.conj i⁻¹).toMonoidHom =
      (MulAut.conj (i.val)⁻¹).toMonoidHom.comp I.subtype := by ext; rfl
  rw [map_map, hc, ← map_map, map_subgroupOf_eq_of_le hVI]

/-- E.2.13(6)'s commuting-conjugate premise follows from the actual global
weak closure. This uses right conjugation and the literal restriction to I. -/
theorem local_conjugates_centralize (I T V : Subgroup G) (hVI : V ≤ I)
    (hw : 0 < globalW V T) (i : I)
    (hi : (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ T.subgroupOf I) :
    (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤
      centralizer (V.subgroupOf I : Set I) := by
  have he := restricted_right_conjugate_image I V hVI i
  have ht : V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≤ T := by
    rw [← he]
    exact (map_mono hi).trans ((subgroupOf_map_subtype T I).le.trans inf_le_left)
  have hc := conjugate_le_centralizer_of_le_sylow_of_globalW_pos hw (i.val)⁻¹ ht
  intro x hx y hy
  apply Subtype.ext
  exact hc (he ▸ mem_map_of_mem I.subtype hx) y.val hy

/-- Restricting the acting group through an injection cannot decrease q.
The vector space is unchanged; no faithfulness of its action is required. -/
private theorem quadraticRatio_le_injective_restriction
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (f : D →* G) (hf : Function.Injective f) :
    quadraticRatio ρ ≤ quadraticRatio (ρ.comp f) := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hquad⟩
  let : IsElementaryAbelian 2 A := hA.2
  have he : IsElementaryTwo (A.map f) :=
    ⟨fun h => hA.1 ((map_eq_bot_iff_of_injective A hf).mp h),
      IsElementaryAbelian.map f⟩
  have hq : IsQuadratic ρ (A.map f) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
    exact hquad a ha b hb v
  have hr : actionRatio ρ (A.map f) = actionRatio (ρ.comp f) A := by
    unfold actionRatio fixedCodim
    rw [fixedSpace_comp_map, rank_map_injective f hf]
  exact (iInf_le_of_le (A.map f) (iInf_le_of_le ⟨he, hq⟩ le_rfl)).trans hr.le

/-- The local ratio premise of E.2.14(7) holds on Aut_{M∩I}(V), as a
literal subgroup of Aut_G(V), whenever the preceding Chapter 7 bound holds. -/
theorem local_quadraticRatio_gt_one (M I V : Subgroup G) [IsElementaryAbelian 2 V]
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp
      (inducedAutomizer V M).subtype)) :
    1 < quadraticRatio ((automizerRepresentation V).comp
      (inducedAutomizer V (M ⊓ I)).subtype) :=
  hq.trans_le (quadraticRatio_le_injective_restriction _
    (Subgroup.inclusion (show inducedAutomizer V (M ⊓ I) ≤ inducedAutomizer V M from
      map_mono (comap_mono inf_le_left))) (Subgroup.inclusion_injective _))

/-- E.2.14(7) uses Aut_I(V), even though I does not normalize V. The
normalizer containment from E.2.9 identifies this image with Aut_{M∩I}(V),
so the preceding bound applies to that exact action. -/
theorem selected_quadraticRatio_gt_one (M I V : Subgroup G) [IsElementaryAbelian 2 V]
    (hNI : I ⊓ normalizer (V : Set G) ≤ M)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp
      (inducedAutomizer V M).subtype)) :
    1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V I).subtype) := by
  have he : inducedAutomizer V I = inducedAutomizer V (M ⊓ I) := by
    unfold inducedAutomizer
    congr 1
    ext x
    change x.val ∈ I ↔ x.val ∈ M ⊓ I
    exact ⟨fun hx => ⟨hNI ⟨hx, x.property⟩, hx⟩, fun hx => hx.2⟩
  rw [he]
  exact local_quadraticRatio_gt_one M I V hq

/-- Apply the proved E.2.10(5) inside the selected subgroup and embed its
conclusion into G. The output actor is exactly V^h ∩ O₂(I), not an
unidentified isomorphic copy. E.2.11(1) supplies the displayed local setup. -/
theorem selected_actor_cubic [Finite G] (I M V : Subgroup G) (hVI : V ≤ I)
    (S : Sylow 2 I) (i : I)
    (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹) :
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    ⁅⁅⁅V, A⁆, A⁆, A⁆ = ⊥ := by
  have ha : (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype =
      V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype := by
    rw [h.A_eq_twoCore_inf, map_inf _ _ _ I.subtype_injective]
    rw [TwoConjugate.W, restricted_right_conjugate_image I V hVI i, inf_comm]
  have hc := congrArg (Subgroup.map I.subtype) h.cubic
  simpa only [map_commutator, map_subgroupOf_eq_of_le hVI, ha, Subgroup.map_bot] using hc

/-- Centralizing a group centralizes every one of its normal sections.
This form retains the embedding of the local two-core in the ambient group. -/
private theorem centralizer_le_core_of_section_bound (I P : Subgroup G)
    (Z : Subgroup I) [Z.Normal]
    (hb : centralizerModulo ⊤ (P.subgroupOf I) Z ≤ pCore 2 I) :
    I ⊓ centralizer (P : Set G) ≤ (pCore 2 I).map I.subtype := by
  rintro x ⟨hxI, hx⟩
  refine ⟨⟨x, hxI⟩, hb ?_, rfl⟩
  apply mem_centralizerModulo_iff.mpr
  refine ⟨mem_top _, ?_⟩
  intro a ha
  have hc := commutatorElement_eq_one_iff_mul_comm.mpr
    (show a * (⟨x, hxI⟩ : I) = (⟨x, hxI⟩ : I) * a from Subtype.ext (hx a.val ha))
  rw [hc]
  exact Z.one_mem

/-- E.2.13(7), once supplied for the actual E.2.10 section, gives the
precise C_I(A join B) bound consumed by `selected_pair_conclusions`.
The section centralizer is inside I, not inside the original ambient group. -/
theorem selected_pair_centralizer_bound [Finite G]
    (I M V : Subgroup G) (hVI : V ≤ I) (S : Sylow 2 I) (i : I)
    (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
    (hb : letI := h.Z_normal
      centralizerModulo ⊤ (TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
        (TwoConjugate.Z (V.subgroupOf I) i⁻¹) ≤ pCore 2 I) :
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    let B := V ⊓ (pCore 2 I).map I.subtype
    I ⊓ centralizer (A ⊔ B : Subgroup G) ≤ (pCore 2 I).map I.subtype := by
  let := h.Z_normal
  have ha : (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype =
      V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype := by
    rw [h.A_eq_twoCore_inf, map_inf _ _ _ I.subtype_injective]
    rw [TwoConjugate.W, restricted_right_conjugate_image I V hVI i, inf_comm]
  have hp : (TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹).map I.subtype =
      (V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) ⊔
        (V ⊓ (pCore 2 I).map I.subtype) := by
    rw [TwoConjugate.P, Subgroup.map_sup, ha, h.B_eq_twoCore_inf,
      map_inf _ _ _ I.subtype_injective, map_subgroupOf_eq_of_le hVI, inf_comm, sup_comm]
  apply centralizer_le_core_of_section_bound I _ (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
  rw [← hp, subgroupOf, comap_map_eq_self_of_injective I.subtype_injective]
  exact hb

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
