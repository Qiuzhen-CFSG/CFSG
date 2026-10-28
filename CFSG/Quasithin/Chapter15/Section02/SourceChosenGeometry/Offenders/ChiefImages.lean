module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefActors

/-!
# Sharp actions of every original offender on both chief factors

Quadratic replacement and literal quotient-image minimality identify the
original actor and its replacement modulo O₂(H). Each noncentral chief
factor kills O₂(H), so their actions on that factor agree. The replacement's
sharp rank identity therefore holds for the original actor, without assuming
that its action on the entire conjugate span is quadratic. Sylow conjugacy
extends the result to every Delta member. Adding the two chief contributions
gives the full-span lower bound used in the remaining equality argument.

These are the original actors and literal chief quotients. The offender-plane
owner retains the full-span quadraticity and marked-factor assembly; the parent
qt-e-152-plane-geometry discharges the preceding small-parabolic inputs.

Source: Aschbacher--Smith D.1.3(3), 15.1.12(2), and 15.2.9,
printed pp.174--175,1090,1110.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem map_eq_of_replacement {L K : Type*} [Group L] [Group K]
    (f : L →* K) {U N A D : Subgroup L}
    (hUN : U ≤ N) (hDA : D ≤ A ⊔ U) (hAD : A ≤ D ⊔ N) (hNk : N ≤ f.ker) :
    A.map f = D.map f := by
  have hN : N.map f = ⊥ := (map_eq_bot_iff N).mpr hNk
  have hU : U.map f = ⊥ := (map_eq_bot_iff U).mpr (hUN.trans hNk)
  apply le_antisymm
  · simpa only [Subgroup.map_sup,hN,sup_bot_eq] using map_mono (f := f) hAD
  · simpa only [Subgroup.map_sup,hU,sup_bot_eq] using map_mono (f := f) hDA

set_option backward.isDefEq.respectTransparency false in
/-- The original Delta actor has the sharp quadratic action on each literal
noncentral chief factor, first inside the specified Sylow subgroup. -/
theorem ChosenSmallSource.delta_chief_actions_in_sylow
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) (hAT : A ≤ (T : Subgroup G))
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    IsQuadratic (s.factorRepresentation i) (A.subgroupOf H) ∧
      Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) =
        fixedCodim (s.factorRepresentation i) (A.subgroupOf H) ∧
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) (A.subgroupOf H)) := by
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
  have hA₀T : A₀ ≤ S := fun _ ha => hAT ha
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hUN : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x,hx,he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  obtain ⟨D,hD,hDN,hDn,hDq,hDA,hAD⟩ := h.delta_quadratic_replacement_in_sylow hH hA hAT
  have hcount : s.noncentralCount = 2 :=
    source_chosen_noncentral_count_two_from_source h.ambient T h.empty h.maximal hH
      h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span h.prepared.le_local hV h.prepared.quadratic_ratio s
  have heq := source_sqtk_multiple_equalities d h.prepared.nontrivial hV
    (Chapter3.sqtk_of_mem_H h.ambient hH.1.1.1) hq S hS s (by omega) D hD hDq hDn
  let ρ := s.factorRepresentation i
  have hP := source_intrinsic_minimalParabolic_of_notFF d h.prepared.nontrivial hnf S hS
  have hkN : pCore 2 H ≤ ρ.ker := by
    have hk := MultipleFactors.source_chief_sylow_kernel U S hP s i hi
      (pCore 2 H) (pCore_isPGroup.le_sylow_of_normal S)
    rw [inf_idem] at hk
    exact hk.ge.trans inf_le_right
  have him : actionSubgroup ρ A₀ = actionSubgroup ρ D :=
    map_eq_of_replacement (Representation.BinaryOffender.actionHom ρ) hUN hDA hAD
      (by rwa [actionHom_ker_eq])
  have hidx : (pCore 2 H).relIndex A₀ = (pCore 2 H).relIndex D := by
    have hm := map_eq_of_replacement (QuotientGroup.mk' (pCore 2 H)) hUN hDA hAD
      (by rw [QuotientGroup.ker_mk'])
    simpa only [←Subgroup.relIndex_ker,QuotientGroup.ker_mk'] using congrArg (fun X : Subgroup (H ⧸ pCore 2 H) => Nat.card X) hm
  have hcod : fixedCodim ρ A₀ = fixedCodim ρ D := by
    rw [←fixedCodim_actionSubgroup,him,fixedCodim_actionSubgroup]
  have hquad := quadratic_actionSubgroup ρ (MultipleFactors.chiefFactor_quadratic U s hDq i)
  rw [←him] at hquad
  have hsharp : Nat.log 2 ((pCore 2 H).relIndex A₀) = fixedCodim ρ A₀ := by
    rw [hidx,hcod]
    exact heq.2.2.2.2.1 i hi
  have hkA := MultipleFactors.source_chief_sylow_kernel U S hP s i hi A₀ hA₀T
  have hAn : ¬ A₀ ≤ ρ.ker := by
    intro hn
    have hAN : A₀ ≤ pCore 2 H := by
      rw [inf_eq_left.mpr hn] at hkA
      exact hkA.le.trans inf_le_right
    have hm := map_mono (f := H.subtype) hAN
    rw [map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hA.2.1 hm
  refine ⟨?_,hsharp,elementary_actionSubgroup ρ hAn,?_⟩
  · intro a ha b hb v
    exact hquad _ (mem_map_of_mem _ ha) _ (mem_map_of_mem _ hb) v
  · rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,
      ←inf_relIndex_left,hkA,inf_relIndex_left]
    exact hsharp.ge

private theorem quadratic_of_conjugate {L W : Type*} [Group L]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W) (A : Subgroup L) (g : L)
    (hq : IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom)) : IsQuadratic ρ A := by
  have hinv (w : W) : ρ g⁻¹ (ρ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hconj (a : L) (w : W) : ρ (g * a * g⁻¹) (ρ g w) = ρ g (ρ a w) := by
    simp only [map_mul,Module.End.mul_apply,hinv]
  intro a ha b hb v
  have hh := hq _ (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
    _ (mem_map_of_mem (MulAut.conj g).toMonoidHom hb) (ρ g v)
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) (ρ g v) - ρ g v) =
    ρ (g * b * g⁻¹) (ρ g v) - ρ g v at hh
  rw [hconj,←map_sub,hconj] at hh
  have he := congrArg (ρ g⁻¹) hh
  simpa only [hinv,map_zero] using he

private theorem actionSubgroup_conjugate {L W : Type*} [Group L]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) L W) (A : Subgroup L) (g : L) :
    actionSubgroup ρ (A.map (MulAut.conj g).toMonoidHom) =
      (actionSubgroup ρ A).map (MulAut.conj (Representation.BinaryOffender.actionHom ρ g)).toMonoidHom := by
  change (A.map _).map _ = (A.map _).map _
  rw [map_map,map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Uniform original-offender chief actions, with their exact quotient rank. -/
theorem ChosenSmallSource.delta_chief_actions
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    IsQuadratic (s.factorRepresentation i) (A.subgroupOf H) ∧
      Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) =
        fixedCodim (s.factorRepresentation i) (A.subgroupOf H) ∧
      IsOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) (A.subgroupOf H)) := by
  let : IsElementaryAbelian 2 A := hA.1.2.1
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1.1
  have hp : IsPGroup 2 A₀ := IsElementaryAbelian.isPGroup 2 A₀
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  let S := T.subtype hH.1.1.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  let e := MulAut.conj (g : G)
  let e₀ := MulAut.conj g
  let B := A.map e.toMonoidHom
  have hB : B ∈ delta H := delta_conjugate hA g.property
  have hPS : (P : Subgroup H).map e₀.toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  have hBT : B ≤ (T : Subgroup G) := by
    have hm := map_mono (f := H.subtype) ((map_mono hP).trans hPS.le)
    rw [map_map,show H.subtype.comp e₀.toMonoidHom =
      e.toMonoidHom.comp H.subtype from rfl,
      ← map_map,map_subgroupOf_eq_of_le hA.1.1] at hm
    exact hm.trans_eq (map_subgroupOf_eq_of_le hH.1.1.2)
  have he := h.delta_chief_actions_in_sylow hH hB hBT s i hi
  have hBm : B.subgroupOf H = A₀.map e₀.toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hB.1.1,map_map,
      show H.subtype.comp e₀.toMonoidHom = e.toMonoidHom.comp H.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hA.1.1]
  rw [hBm] at he
  have hQ : (pCore 2 H).map e₀.toMonoidHom = pCore 2 H := by
    exact Subgroup.Normal.map_conj_eq (pCore 2 H) g
  have hidx : (pCore 2 H).relIndex (A₀.map e₀.toMonoidHom) = (pCore 2 H).relIndex A₀ := by
    simpa only [hQ] using relIndex_map_map_of_injective
      (f := e₀.toMonoidHom) (pCore 2 H) A₀ e₀.injective
  have hsharp : Nat.log 2 ((pCore 2 H).relIndex A₀) = fixedCodim (s.factorRepresentation i) A₀ := by
    simpa only [hidx,e₀,fixedCodim_map_conj] using he.2.1
  have hAm := actionSubgroup_conjugate (s.factorRepresentation i) A₀ g
  have hrank : rank (actionSubgroup (s.factorRepresentation i) (A₀.map e₀.toMonoidHom)) =
      rank (actionSubgroup (s.factorRepresentation i) A₀) := by
    rw [hAm,rank_map_conj]
  have hne : actionSubgroup (s.factorRepresentation i) A₀ ≠ ⊥ := by
    intro hb
    apply he.2.2.1.1
    rw [hAm,hb,Subgroup.map_bot]
  refine ⟨quadratic_of_conjugate _ A₀ g he.1,hsharp,⟨hne,IsElementaryAbelian.map _⟩,?_⟩
  have hb := he.2.2.2
  simpa only [fixedCodim_actionSubgroup,e₀,fixedCodim_map_conj,hrank] using hb

set_option backward.isDefEq.respectTransparency false in
/-- Both noncentral chief factors contribute the original quotient-image rank
to the fixed codimension on the entire conjugate span. -/
theorem ChosenSmallSource.delta_chief_rank_lower
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) :
    2 * Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) ≤
      fixedCodim (normalRepresentation ((conjugateSpan H V).subgroupOf H)) (A.subgroupOf H) := by
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hc : s.noncentralCount = 2 :=
    source_chosen_noncentral_count_two_from_source h.ambient T h.empty h.maximal hH
      h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span h.prepared.le_local (h.prepared.inside_core H hH)
      h.prepared.quadratic_ratio s
  have hl := qrc_chief_factor_lower U s (A.subgroupOf H)
    (Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)))
    (fun i hi => by exact_mod_cast (h.delta_chief_actions hH hA s i hi).2.1.le)
  rw [hc] at hl
  exact_mod_cast hl

set_option backward.isDefEq.respectTransparency false in
/-- Each original Delta image is a source FF-star offender of ratio one on
both noncentral chief factors. -/
theorem ChosenSmallSource.delta_chief_bestOffender
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    IsBestOffender (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) (A.subgroupOf H)) ∧
      actionRatio (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) (A.subgroupOf H)) = 1 := by
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
  have hbound := (source_sqtk_chief_actions d h.prepared.nontrivial hV hnf
    (Chapter3.sqtk_of_mem_H h.ambient hH.1.1.1) S hS s i).1
  let ρ := Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i)
  let E := actionSubgroup (s.factorRepresentation i) (A.subgroupOf H)
  have hoff : IsOffender ρ E := (h.delta_chief_actions hH hA s i hi).2.2
  have hns : ¬ IsStrongFFModule ρ := by
    intro hs
    exact (not_lt_of_ge hbound) ((isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs)
  have heq : fixedCodim ρ E = rank E := le_antisymm hoff.2
    (Nat.le_of_not_gt fun hl => hns ⟨E,hoff.1,hl⟩)
  exact ⟨(isBestOffender_iff_of_not_strong ρ hns E).mpr ⟨hoff.1,heq⟩,
    (actionRatio_eq_one_iff ρ hoff.1).mpr heq⟩

end CFSG.Quasithin.Chapter15.Section02
