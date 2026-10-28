module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.SpanActions
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.Construction
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions.Cyclic.Transport
public import Theory.Representation.BinaryOffender.TimmesfeldCentralizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Quadraticity and sharp ranks for every original Delta offender

Apply Timmesfeld replacement to the full action of the original actor A.
The lifted displacement centralizer D has the same two-core quotient image
and centralizes [U_H,A]; commutativity of their action images also makes A
centralize [U_H,D]. If A is outside T, so is D. The nontrivial quadratic
D-intersection has equal fixed and moved planes on the chosen four-space.
The two cross identities then make A centralize [V,A∩O₂(H)].

Conjugacy proves this on every generator V^g of U_H. Relative generation,
the Three Subgroups Lemma and the already proved fixed-centralizer equality
give [[U_H,A],A]=1 for the original A. The source equality theorem now gives
both sharp full-span rank identities, with Sylow conjugacy preserving the
literal quotient and centralizer indices.

The preceding actual wreath quotient is supplied by qt-e-152-small-parabolic
and discharged by qt-e-152-plane-geometry. This module supplies the uniform
quadraticity premise of the actual plane consumer. Order-two quotient images
and simultaneous marked chief-factor identifications remain with this owner.

Sources: Aschbacher--Smith D.1.3(3), 15.1.12(2), 15.2.9--11,
printed pp.174--175,1090,1110--1111; GLS2, Theorem26.23(i), for the
full displacement-centralizer form of replacement.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem twoCore_le_chosenSylow {T : Sylow 2 G} {M H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) : twoCoreIn H ≤ (T : Subgroup G) := by
  have hh := map_mono (f := H.subtype)
    (pCore_isPGroup.le_sylow_of_normal (T.subtype hH.1.1.2))
  change (pCore 2 H).map H.subtype ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
  rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh

omit [Finite G] in
private theorem action_cross_commutator (U A D : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U]
    (hc : ∀ d ∈ D, ∀ a ∈ A, ∀ v : Additive U,
      normalRepresentation U d (normalRepresentation U a v - v) =
        normalRepresentation U a v - v) :
    ⁅⁅U,A⁆,D⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer,commutator_comm U A]
  apply commutator_le.mpr
  intro a ha u hu d hd
  have hh := congrArg (fun v : Additive U => (v.toMul : G))
    (hc d hd a ha (Additive.ofMul ⟨u,hu⟩))
  change d * (a * u * a⁻¹ / u) * d⁻¹ = a * u * a⁻¹ / u at hh
  simpa only [div_eq_mul_inv,commutatorElement_def] using mul_inv_eq_iff_eq_mul.mp hh

set_option backward.isDefEq.respectTransparency false in
/-- A quadratic lift of the full displacement centralizer, preserving the
original quotient image and both actual cross-commutator identities. -/
theorem ChosenSmallSource.delta_displacement_replacement
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) (hA : A ∈ delta H) :
    ∃ D ∈ delta H, offenderImage H D = offenderImage H A ∧
      ⁅⁅conjugateSpan H V,D⁆,D⁆ = ⊥ ∧
      ⁅⁅conjugateSpan H V,A⁆,D⁆ = ⊥ ∧
      ⁅⁅conjugateSpan H V,D⁆,A⁆ = ⊥ := by
  let := h.prepared.elementary
  let d := source_chosenNormalizer_qrcConfiguration h.ambient T h.empty h.maximal
    h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
    h.prepared.seed_span hH
  have hq := (source_chosen_equality_inputs h.ambient T h.empty h.maximal hH h.centralizing
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
    h.prepared.le_local h.prepared.quadratic_ratio).1
  have hnf := source_notFF_of_ratio_two d hq
  have hV := h.prepared.inside_core H hH
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let ρ := normalRepresentation U
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let f := Representation.BinaryOffender.actionHom ρ
  let I := actionSubgroup ρ (A.subgroupOf H)
  have hI : IsBestOffender σ I := (h.delta_span_action hH hA).1
  let E := displacementCentralizer σ I
  have hE := hI.displacementCentralizer_isBestOffender σ
  have hEI : E ≤ I := displacementCentralizer_le σ I
  obtain ⟨D,hD,_,hDQ,hDE⟩ := h.delta_lift_span_bestOffender hH hA E hE hEI
  have hcross : ∀ x ∈ D.subgroupOf H, ∀ a ∈ A.subgroupOf H, ∀ v : Additive U,
      ρ x (ρ a v - v) = ρ a v - v := by
    intro x hx a ha v
    have hxE : f x ∈ E := hDE ▸ mem_map_of_mem f hx
    exact hxE.2 (f a) (mem_map_of_mem f ha) v
  have hback : ∀ a ∈ A.subgroupOf H, ∀ x ∈ D.subgroupOf H, ∀ v : Additive U,
      ρ a (ρ x v - v) = ρ x v - v := by
    intro a ha x hx v
    have hxI : f x ∈ I := hEI (hDE ▸ mem_map_of_mem f hx)
    have hax := displacement_commute σ hI.1 (mem_map_of_mem f ha) hxI v
    change ρ a (ρ x v - v) - (ρ x v - v) =
      ρ x (ρ a v - v) - (ρ a v - v) at hax
    rw [hcross x hx a ha v,sub_self] at hax
    exact sub_eq_zero.mp hax
  have hquad : IsQuadratic ρ (D.subgroupOf H) := by
    intro x hx y hy v
    have hxE : f x ∈ E := hDE ▸ mem_map_of_mem f hx
    have hyE : f y ∈ E := hDE ▸ mem_map_of_mem f hy
    exact (displacementCentralizer_isQuadratic σ I) (f x) hxE (f y) hyE v
  have hmap (P Q : Subgroup G) (hP : P ≤ H) (hQ : Q ≤ H)
      (hc : ⁅⁅U,P.subgroupOf H⁆,Q.subgroupOf H⁆ = ⊥) :
      ⁅⁅conjugateSpan H V,P⁆,Q⁆ = ⊥ := by
    have hm := congrArg (Subgroup.map H.subtype) hc
    rwa [Subgroup.map_commutator,Subgroup.map_commutator,
      map_subgroupOf_eq_of_le hP,map_subgroupOf_eq_of_le hQ,
      map_subgroupOf_eq_of_le ((span_le_right_core d hV).trans (twoCore_le H)),Subgroup.map_bot] at hm
  exact ⟨D,hD,hDQ,
    hmap D D hD.1.1 hD.1.1 (action_cross_commutator U _ _ hquad),
    hmap A D hA.1.1 hD.1.1 (action_cross_commutator U _ _ hcross),
    hmap D A hD.1.1 hA.1.1 (action_cross_commutator U _ _ hback)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original actor centralizes its two-core displacement on V. -/
theorem ChosenSmallSource.delta_local_core_cross
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A ∈ delta H) :
    ⁅⁅V,A ⊓ twoCoreIn H⁆,A⁆ = ⊥ := by
  let := h.prepared.elementary
  by_cases hAT : A ≤ (T : Subgroup G)
  · have hc := h.sigmaAt_centralizes hH (show A ⊓ twoCoreIn H ∈ sigmaAt (T : Subgroup G) H from
      ⟨A,⟨hA,hAT⟩,rfl⟩)
    have hz : ⁅V,A ⊓ twoCoreIn H⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    rw [hz,commutator_bot_left]
  obtain ⟨D,hD,hDQ,hDq,hcross,hback⟩ := h.delta_displacement_replacement hH hA
  have hQT := twoCore_le_chosenSylow hH
  have hDT : ¬ D ≤ (T : Subgroup G) := by
    intro ht
    have hh := (offenderImage_le_iff hA.1.1 hD.1.1).mp hDQ.ge
    exact hAT (hh.trans (sup_le ht hQT))
  let F := D ⊓ twoCoreIn H
  let : IsElementaryAbelian 2 D := hD.1.2.1
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (inf_le_left : F ≤ D)
  have hFT : F ≤ (T : Subgroup G) := inf_le_right.trans hQT
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hNV := (h.wreath_intersections hH he).2
  have hmove : ¬ F ≤ centralizer (V : Set G) := by
    intro hc
    have hh := le_inf hVU (le_centralizer_iff.mp hc)
    rw [←h.delta_fixed hH hD] at hh
    apply hDT
    rw [←hNV]
    exact le_inf hD.1.1 ((le_centralizer_iff.mp (hh.trans inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hq := actor_quadratic (D := F) h.prepared.normalized hVU inf_le_left hDq
  have hi : IsElementaryTwo (actor M V F h.prepared.normalized) :=
    ⟨actor_nontrivial _ (hFT.trans h.maximal.1.2) hmove,
      actor_elementary _ (hFT.trans h.maximal.1.2)⟩
  have hfixed := ChosenGeometry.Cyclic.ambient_fixed_eq_commutator h
    (hFT.trans h.maximal.1.2) hi hq
  have hBV : A ⊓ twoCoreIn H ≤ normalizer (V : Set G) :=
    (inf_le_right.trans hQT).trans (h.maximal.1.2.trans h.prepared.normalized)
  have hZ : ⁅V,A ⊓ twoCoreIn H⁆ ≤ V ⊓ centralizer (F : Set G) := by
    refine le_inf (le_normalizer_iff_commutator_le_left.mp hBV) ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    exact (commutator_mono (commutator_mono hVU inf_le_left) inf_le_left).trans hcross.le
  rw [hfixed] at hZ
  apply bot_unique
  exact (commutator_mono (hZ.trans (commutator_mono hVU inf_le_left)) le_rfl).trans hback.le

set_option backward.isDefEq.respectTransparency false in
/-- Every original inclusion-minimal quotient-image offender is quadratic on
the entire conjugate span, under the preceding actual wreath quotient. -/
theorem ChosenSmallSource.delta_quadratic
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hA : A ∈ delta H) : ⁅⁅conjugateSpan H V,A⁆,A⁆ = ⊥ := by
  let := h.prepared.elementary
  let U := conjugateSpan H V
  let B := A ⊓ twoCoreIn H
  let C := U ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U :=
    (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hH).1
  let : IsElementaryAbelian 2 A := hA.1.2.1
  have hUA : A ≤ normalizer (U : Set G) := hA.1.1.trans (conjugateSpan_normalized H V)
  have hUB : B ≤ normalizer (U : Set G) := inf_le_left.trans hUA
  have hUC : U ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro u hu c hc
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨c,hc.1⟩ : U) ⟨u,hu⟩)
  have hlocal (g : H) : ⁅V.map (MulAut.conj (g : G)).toMonoidHom,B⁆ ≤ C := by
    have hc := h.delta_local_core_cross hH he (delta_conjugate hA (H.inv_mem g.property))
    let e := MulAut.conj (g : G)
    have hN : (twoCoreIn H).map e.toMonoidHom = twoCoreIn H :=
      mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H g.property)
    have hcancel : e.toMonoidHom.comp (MulAut.conj (g : G)⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [e,MulAut.conj_apply,mul_assoc]
    have hm := congrArg (Subgroup.map e.toMonoidHom) hc
    rw [Subgroup.map_commutator,Subgroup.map_commutator,
      Subgroup.map_inf _ _ _ e.injective,map_map,hcancel,Subgroup.map_id,hN,Subgroup.map_bot] at hm
    refine le_inf ?_ (commutator_eq_bot_iff_le_centralizer.mp hm)
    exact (commutator_mono (le_iSup (fun g : H =>
      V.map (MulAut.conj (g : G)).toMonoidHom) g) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hUB)
  have hUBA : ⁅⁅U,B⁆,A⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (commutator_iSup_le_of_relative_normal U B C
      (fun g : H => V.map (MulAut.conj (g : G)).toMonoidHom) hUC
      (fun g => (le_iSup (fun g : H =>
        V.map (MulAut.conj (g : G)).toMonoidHom) g)) hlocal).trans inf_le_right
  have hBA : ⁅B,A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono inf_le_left le_rfl).trans (commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative A)).le
  have hUAB : ⁅⁅U,A⁆,B⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · rw [commutator_comm A B,hBA,commutator_bot_left]
    · simpa only [commutator_comm B U] using hUBA
  have hh : ⁅U,A⁆ ≤ U ⊓ centralizer (B : Set G) :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hUA)
      (commutator_eq_bot_iff_le_centralizer.mp hUAB)
  rw [←h.delta_fixed hH hA] at hh
  exact commutator_eq_bot_iff_le_centralizer.mpr (hh.trans inf_le_right)


omit [Finite G] in
private theorem normal_quadratic_of_double (U A : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (hq : ⁅⁅U,A⁆,A⁆ = ⊥) :
    IsQuadratic (normalRepresentation U) A := by
  have hc : A ≤ centralizer (⁅U,A⁆ : Subgroup G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hq)
  intro a ha b hb v
  apply Additive.toMul.injective
  apply Subtype.ext
  change a * (b * (v.toMul : G) * b⁻¹ / (v.toMul : G)) * a⁻¹ =
    b * (v.toMul : G) * b⁻¹ / (v.toMul : G)
  simp only [div_eq_mul_inv]
  have hm : ⁅b,(v.toMul : G)⁆ ∈ ⁅U,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hb v.toMul.property
  change a * ⁅b,(v.toMul : G)⁆ * a⁻¹ = ⁅b,(v.toMul : G)⁆
  rw [(hc ha _ hm).symm,mul_inv_cancel_right]

set_option backward.isDefEq.respectTransparency false in
/-- Both sharp whole-span rank identities for the original actor, in the
specified Sylow subgroup. Quadraticity is proved, not supplied as a callback. -/
theorem ChosenSmallSource.delta_span_ranks_in_sylow
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) (hAT : A ≤ (T : Subgroup G)) :
    let U := (conjugateSpan H V).subgroupOf H
    2 * Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) =
      fixedCodim (normalRepresentation U) (A.subgroupOf H) ∧
    fixedCodim (normalRepresentation U) (A.subgroupOf H) =
      2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A.subgroupOf H ⊓ pCore 2 H)) := by
  let := h.prepared.elementary
  let d := source_chosenNormalizer_qrcConfiguration h.ambient T h.empty h.maximal
    h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
    h.prepared.seed_span hH
  have hq := (source_chosen_equality_inputs h.ambient T h.empty h.maximal hH h.centralizing
    h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized h.prepared.seed_span
    h.prepared.le_local h.prepared.quadratic_ratio).1
  have hnf := source_notFF_of_ratio_two d hq
  have hV := h.prepared.inside_core H hH
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let S := T.subtype hH.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le hH.1.1.2
  let A₀ := A.subgroupOf H
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups (S : Subgroup H) := by
    apply (maxFamily_sylow_iff S A₀).mpr
    refine ⟨fun a ha => hAT ha, ?_⟩
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  have hAn : ¬ A₀ ≤ centralizer (U : Set H) := by
    intro hc
    have hn := (le_inf hA₀.1 hc).trans
      (source_span_centralizer_sylow_le_core d h.prepared.nontrivial hV hnf S hS)
    have hm := map_mono (f := H.subtype) hn
    rw [map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hA.2.1 hm
  have hquad : IsQuadratic (normalRepresentation U) A₀ := by
    apply normal_quadratic_of_double
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator,Subgroup.map_commutator,
      map_subgroupOf_eq_of_le hA.1.1,
      map_subgroupOf_eq_of_le ((span_le_right_core d hV).trans (twoCore_le H)),Subgroup.map_bot]
    exact h.delta_quadratic hH he hA
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hc : s.noncentralCount = 2 :=
    source_chosen_noncentral_count_two_from_source h.ambient T h.empty h.maximal hH
      h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span h.prepared.le_local hV h.prepared.quadratic_ratio s
  have hsharp := source_sqtk_multiple_equalities d h.prepared.nontrivial hV
    (Chapter3.sqtk_of_mem_H h.ambient hH.1.1.1) hq S hS s (by omega) A₀ hA₀ hquad hAn
  exact ⟨hsharp.2.1,hsharp.2.2.1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original uniform total displacement and two-core action ranks of
15.1.12(2), retaining literal relative indices inside H. -/
theorem ChosenSmallSource.delta_span_ranks
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) :
    let U := (conjugateSpan H V).subgroupOf H
    2 * Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) =
      fixedCodim (normalRepresentation U) (A.subgroupOf H) ∧
    fixedCodim (normalRepresentation U) (A.subgroupOf H) =
      2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A.subgroupOf H ⊓ pCore 2 H)) := by
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
  let S := T.subtype hH.1.1.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  let e := MulAut.conj (g : G)
  let e₀ := MulAut.conj g
  let D := A.map e.toMonoidHom
  have hD : D ∈ delta H := delta_conjugate hA g.property
  have hPS : (P : Subgroup H).map e₀.toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  have hDT : D ≤ (T : Subgroup G) := by
    have hm := map_mono (f := H.subtype) ((map_mono hP).trans hPS.le)
    rw [map_map,show H.subtype.comp e₀.toMonoidHom =
      e.toMonoidHom.comp H.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hm.trans_eq (map_subgroupOf_eq_of_le hH.1.1.2)
  have hh := h.delta_span_ranks_in_sylow hH he hD hDT
  have hDm : D.subgroupOf H = A₀.map e₀.toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hD.1.1,map_map,
      show H.subtype.comp e₀.toMonoidHom = e.toMonoidHom.comp H.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hA.1.1]
  rw [hDm] at hh
  let U := (conjugateSpan H V).subgroupOf H
  have hQ : (pCore 2 H).map e₀.toMonoidHom = pCore 2 H :=
    Subgroup.Normal.map_conj_eq (pCore 2 H) g
  have hC : (centralizer (U : Set H)).map e₀.toMonoidHom = centralizer (U : Set H) :=
    Subgroup.Normal.map_conj_eq _ g
  have hidx : (pCore 2 H).relIndex (A₀.map e₀.toMonoidHom) = (pCore 2 H).relIndex A₀ := by
    simpa only [hQ] using relIndex_map_map_of_injective
      (f := e₀.toMonoidHom) (pCore 2 H) A₀ e₀.injective
  have hidxB : (centralizer (U : Set H)).relIndex (A₀.map e₀.toMonoidHom ⊓ pCore 2 H) =
      (centralizer (U : Set H)).relIndex (A₀ ⊓ pCore 2 H) := by
    have hi := relIndex_map_map_of_injective
      (f := e₀.toMonoidHom) (centralizer (U : Set H)) (A₀ ⊓ pCore 2 H) e₀.injective
    rw [Subgroup.map_inf _ _ e₀.toMonoidHom e₀.injective,hQ,hC] at hi
    exact hi
  change 2 * Nat.log 2 ((pCore 2 H).relIndex (A₀.map e₀.toMonoidHom)) =
      fixedCodim (normalRepresentation U) (A₀.map e₀.toMonoidHom) ∧
    fixedCodim (normalRepresentation U) (A₀.map e₀.toMonoidHom) =
      2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A₀.map e₀.toMonoidHom ⊓ pCore 2 H)) at hh
  rw [hidx,hidxB] at hh
  simpa only [e₀,fixedCodim_map_conj] using hh


end CFSG.Quasithin.Chapter15.Section02
