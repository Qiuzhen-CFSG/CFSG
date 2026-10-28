module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Offenders.ChiefImages

/-!
# Whole-span weights and literal lifts for original offenders

Every moving maximum elementary subgroup has action ratio one on the entire
conjugate span. To prove this, choose an equal-weight minimal best offender and
lift it to a quadratic maximum subgroup. The two sharp source rank equalities
make that replacement's weight equal to the module dimension, and equal weight
returns the same conclusion for the original actor. Sylow conjugacy makes the
assertion uniform.

Consequently every best offender in a Delta member's full action has equal
weight and lifts to a maximum elementary subgroup inside its join with the
span. Inclusion-minimality modulo the two-core makes that lift another literal
Delta member with the same quotient image. This controls the replacement's
actual full action; it does not assert quadraticity of the original member.
The Quadratic consumer uses this lift for the full displacement centralizer,
retaining cross-commutator identities to prove the original actor quadratic.
The marked-factor obligations remain with qt-e-152-offender-plane;
qt-e-152-plane-geometry owns the final source assembly.

Source: Aschbacher--Smith B.1.4(3), B.2.8--9, D.1.3(3), and 15.1.12(2),
printed pp.68--69,77,173--175,1089--1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section02
open ChosenGeometry Section01 ChapterD ChapterD.UniqueFactor
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normal_image_representation (U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] :
    NormalElementaryQuotient.representation U (Representation.BinaryOffender.actionHom
      (normalRepresentation U)) (normalRepresentation U).asGroupHom.rangeRestrict_surjective
      ((actionHom_ker_eq _).trans (MultipleFactors.normalRepresentation_ker U)) =
    Representation.BinaryOffender.imageRepresentation (normalRepresentation U) := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨x,rfl⟩ := (normalRepresentation U).asGroupHom.rangeRestrict_surjective g
  apply Additive.toMul.injective
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply U _ _ _ x v

set_option backward.isDefEq.respectTransparency false in
/-- Moving maximum actors in the original Sylow subgroup are best offenders
of ratio one on the entire span, even before their quadraticity is known. -/
theorem ChosenSmallSource.maximum_span_action_in_sylow
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ elementaryAbelianMaxSubgroups H) (hAT : A ≤ (T : Subgroup G))
    (hAN : ¬ A ≤ twoCoreIn H) :
    let ρ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
    IsBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
      (actionSubgroup ρ (A.subgroupOf H)) ∧
    fixedCodim ρ (A.subgroupOf H) = rank (actionSubgroup ρ (A.subgroupOf H)) := by
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
      map_subgroupOf_eq_of_le hA.1] using hA
  have hUS : U ≤ S := fun u hu =>
    (right_core_le_sylow d) ((span_le_right_core d hV) hu)
  have hAn : ¬ A₀ ≤ centralizer (U : Set H) := by
    intro hc
    have hn := (le_inf hA₀.1 hc).trans
      (source_span_centralizer_sylow_le_core d h.prepared.nontrivial hV hnf S hS)
    have hm := map_mono (f := H.subtype) hn
    rw [map_subgroupOf_eq_of_le hA.1] at hm
    exact hAN hm
  let ρ := normalRepresentation U
  let f := Representation.BinaryOffender.actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker = centralizer (U : Set H) :=
    (actionHom_ker_eq _).trans (MultipleFactors.normalRepresentation_ker U)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hσ : NormalElementaryQuotient.representation U f hf hk = σ :=
    normal_image_representation U
  have hne : A₀.map f ≠ ⊥ := fun he => hAn (hk ▸ (map_eq_bot_iff A₀).mp he)
  have hb : IsBestOffender σ (A₀.map f) := by
    rw [←hσ]
    exact maxElementary_isBestOffender U f hf hk S A₀ hUS hA₀ hne
  obtain ⟨E,hE,hEA⟩ := hb.exists_minimal σ
  let D := (A₀ ⊓ E.comap f) ⊔ (U ⊓ centralizer (A₀ ⊓ E.comap f : Set H))
  have hEq : EqualWeightLE (NormalElementaryQuotient.representation U f hf hk) E
      (A₀.map f) := hσ ▸ hEA
  obtain ⟨hD,hDE⟩ := ChapterB.lemma_B_2_8_construct U f hf hk S hUS A₀ hA₀ E hE.1.1 hEq
  have hDn : ¬ D ≤ centralizer (U : Set H) := by
    intro hn
    exact hE.1.1.1 (hDE.symm.trans ((map_eq_bot_iff D).mpr (hk.symm ▸ hn)))
  have hDq : IsQuadratic ρ D := by
    have hh := hE.isQuadratic σ
    intro a ha b hb v
    exact hh (f a) (hDE ▸ mem_map_of_mem f ha) (f b) (hDE ▸ mem_map_of_mem f hb) v
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hc : s.noncentralCount = 2 :=
    source_chosen_noncentral_count_two_from_source h.ambient T h.empty h.maximal hH
      h.centralizing h.prepared.le_selected h.prepared.nontrivial h.prepared.normalized
      h.prepared.seed_span h.prepared.le_local hV h.prepared.quadratic_ratio s
  have heq := source_sqtk_multiple_equalities d h.prepared.nontrivial hV
    (Chapter3.sqtk_of_mem_H h.ambient hH.1.1.1) hq S hS s (by omega) D hD hDq hDn
  let : IsElementaryAbelian 2 D := hD.2.1
  have hker : D ⊓ centralizer (U : Set H) ≤ pCore 2 H :=
    (inf_le_inf_right _ hD.1).trans
      (source_span_centralizer_sylow_le_core d h.prepared.nontrivial hV hnf S hS)
  have hr := MultipleFactors.action_rank_decomposition U D (pCore 2 H) hker
  have hrD : rank E = fixedCodim σ E := by
    rw [←hDE]
    change rank (actionSubgroup ρ D) = fixedCodim σ (actionSubgroup ρ D)
    rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,
      MultipleFactors.normalRepresentation_ker]
    have he1 := heq.2.1
    have he2 := heq.2.2.1
    exact_mod_cast (show (Nat.log 2 ((centralizer (U : Set H)).relIndex D) : ℝ) =
      fixedCodim (normalRepresentation U) D by
        have h1 : (2 : ℝ) * Nat.log 2 ((pCore 2 H).relIndex D) =
            fixedCodim (normalRepresentation U) D := by exact_mod_cast he1
        have h2 : (fixedCodim (normalRepresentation U) D : ℝ) =
            2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (D ⊓ pCore 2 H)) := by
          exact_mod_cast he2
        linarith)
  have hEF := fixedCodim_add_finrank σ E
  have hAF := fixedCodim_add_finrank σ (A₀.map f)
  have hw := hEA.2
  unfold weight at hw
  refine ⟨hb,?_⟩
  change fixedCodim ρ A₀ = rank (A₀.map f)
  have hh : fixedCodim σ (A₀.map f) = rank (A₀.map f) := by omega
  exact (fixedCodim_actionSubgroup ρ A₀).symm.trans hh

private theorem actionSubgroup_map_conj {L W : Type*} [Group L]
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
/-- Whole-span best-offender status and the sharp faithful-action rank for
every maximum actor outside the two-core. -/
theorem ChosenSmallSource.maximum_span_action
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ elementaryAbelianMaxSubgroups H) (hAN : ¬ A ≤ twoCoreIn H) :
    let ρ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
    IsBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
      (actionSubgroup ρ (A.subgroupOf H)) ∧
    fixedCodim ρ (A.subgroupOf H) = rank (actionSubgroup ρ (A.subgroupOf H)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let A₀ := A.subgroupOf H
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hA.1
  obtain ⟨P,hP⟩ := (IsElementaryAbelian.isPGroup 2 A₀).exists_le_sylow
  let S := T.subtype hH.1.1.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H P S
  let e := MulAut.conj (g : G)
  let e₀ := MulAut.conj g
  let B := A.map e.toMonoidHom
  have hHc : H.map e.toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer g.property)
  have hB : B ∈ elementaryAbelianMaxSubgroups H := by
    rw [←hHc]
    exact (maxFamily_map_injective_iff e.toMonoidHom e.injective H A).mpr hA
  have hBN : ¬ B ≤ twoCoreIn H := by
    intro hn
    have heN : (twoCoreIn H).map e.symm.toMonoidHom = twoCoreIn H := by
      have hn' : (twoCoreIn H).map e.toMonoidHom = twoCoreIn H :=
        mem_normalizer_iff_map_conj_eq.mp (twoCore_normalized H g.property)
      have hm := congrArg (Subgroup.map e.symm.toMonoidHom) hn'
      simpa [map_map] using hm.symm
    have hm := map_mono (f := e.symm.toMonoidHom) hn
    rw [heN,map_map] at hm
    exact hAN (by simpa [B,e] using hm)
  have hPS : (P : Subgroup H).map e₀.toMonoidHom = S := by
    change ((g • P : Sylow 2 H) : Subgroup H) = _
    rw [hg]
  have hBT : B ≤ (T : Subgroup G) := by
    have hm := map_mono (f := H.subtype) ((map_mono hP).trans hPS.le)
    rw [map_map,show H.subtype.comp e₀.toMonoidHom =
      e.toMonoidHom.comp H.subtype from rfl,
      ← map_map,map_subgroupOf_eq_of_le hA.1] at hm
    exact hm.trans_eq (map_subgroupOf_eq_of_le hH.1.1.2)
  have he := h.maximum_span_action_in_sylow hH hB hBT hBN
  have hBm : B.subgroupOf H = A₀.map e₀.toMonoidHom := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hB.1,map_map,
      show H.subtype.comp e₀.toMonoidHom = e.toMonoidHom.comp H.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hA.1]
  rw [hBm] at he
  let ρ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let E := actionSubgroup ρ A₀
  have him := actionSubgroup_map_conj ρ A₀ g
  have he' : IsBestOffender σ (E.map (MulAut.conj
      (Representation.BinaryOffender.actionHom ρ g)).toMonoidHom) := him ▸ he.1
  have hb := he'.map_conj σ (Representation.BinaryOffender.actionHom ρ g)⁻¹
  have hcancel : (MulAut.conj (Representation.BinaryOffender.actionHom ρ g)⁻¹).toMonoidHom.comp
      (MulAut.conj (Representation.BinaryOffender.actionHom ρ g)).toMonoidHom =
        MonoidHom.id _ := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [map_map,hcancel,Subgroup.map_id] at hb
  refine ⟨hb,?_⟩
  have heq := he.2
  rw [him,rank_map_conj] at heq
  simpa only [e₀,fixedCodim_map_conj] using heq

set_option backward.isDefEq.respectTransparency false in
/-- In particular, every original Delta actor has full action ratio one. -/
theorem ChosenSmallSource.delta_span_action
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H) :
    let ρ := normalRepresentation ((conjugateSpan H V).subgroupOf H)
    IsBestOffender (Representation.BinaryOffender.imageRepresentation ρ)
      (actionSubgroup ρ (A.subgroupOf H)) ∧
    fixedCodim ρ (A.subgroupOf H) = rank (actionSubgroup ρ (A.subgroupOf H)) ∧
    actionRatio (Representation.BinaryOffender.imageRepresentation ρ)
      (actionSubgroup ρ (A.subgroupOf H)) = 1 := by
  obtain ⟨hb,he⟩ := h.maximum_span_action hH hA.1 hA.2.1
  exact ⟨hb,he,(actionRatio_eq_one_iff _ hb.1).mpr
    ((fixedCodim_actionSubgroup _ _).trans he)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every best offender inside the original full action lifts to another literal
Delta member, retaining the original image modulo O₂(H). -/
theorem ChosenSmallSource.delta_lift_span_bestOffender
    {T : Sylow 2 G} {M Mc V H A : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
    (hA : A ∈ delta H)
    (E : Subgroup (actionImage (normalRepresentation ((conjugateSpan H V).subgroupOf H))))
    (hE : IsBestOffender (Representation.BinaryOffender.imageRepresentation
      (normalRepresentation ((conjugateSpan H V).subgroupOf H))) E)
    (hEA : E ≤ actionSubgroup (normalRepresentation ((conjugateSpan H V).subgroupOf H))
      (A.subgroupOf H)) :
    ∃ D ∈ delta H, D ≤ A ⊔ conjugateSpan H V ∧
      offenderImage H D = offenderImage H A ∧
      actionSubgroup (normalRepresentation ((conjugateSpan H V).subgroupOf H))
        (D.subgroupOf H) = E := by
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
  have hA₀ : A₀ ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H) := by
    apply (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ A₀).mp
    simpa only [A₀,←MonoidHom.range_eq_map,range_subtype,
      map_subgroupOf_eq_of_le hA.1.1] using hA.1
  let ρ := normalRepresentation U
  let f := Representation.BinaryOffender.actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker = centralizer (U : Set H) :=
    (actionHom_ker_eq _).trans (MultipleFactors.normalRepresentation_ker U)
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  have hσ : NormalElementaryQuotient.representation U f hf hk = σ :=
    normal_image_representation U
  obtain ⟨hb,he,_⟩ := h.delta_span_action hH hA
  have he' : fixedCodim σ (A₀.map f) = rank (A₀.map f) :=
    (fixedCodim_actionSubgroup ρ A₀).trans he
  have hwA : weight σ (A₀.map f) = Module.finrank (ZMod 2) (Additive U) := by
    have hh := fixedCodim_add_finrank σ (A₀.map f)
    unfold weight
    omega
  have hEW : EqualWeightLE σ E (A₀.map f) := by
    refine ⟨hEA,le_antisymm (hb.2 E hEA) ?_⟩
    rw [hwA]
    exact (fixedCodim_le_rank_iff σ E).mp (hE.isOffender σ).2
  let D := (A₀ ⊓ E.comap f) ⊔ (U ⊓ centralizer (A₀ ⊓ E.comap f : Set H))
  obtain ⟨hD,hDE⟩ := ChapterB.lemma_B_2_8_construct U f hf hk ⊤ le_top A₀ hA₀ E
    hE.1 (hσ ▸ hEW)
  have hDN : ¬ D ≤ pCore 2 H := by
    intro hn
    have hDS : D ∈ elementaryAbelianMaxSubgroups (S : Subgroup H) :=
      (maxFamily_sylow_iff S D).mpr ⟨hn.trans (pCore_isPGroup.le_sylow_of_normal S),hD⟩
    have hc := source_max_actor_in_core_centralizes d hnf S hS D hDS hn
    exact hE.1.1 (hDE.symm.trans ((map_eq_bot_iff D).mpr (hk.symm ▸ hc)))
  have hDm : D.map H.subtype ∈ elementaryAbelianMaxSubgroups H := by
    have hh := (maxFamily_map_injective_iff H.subtype H.subtype_injective ⊤ D).mpr hD
    simpa only [←MonoidHom.range_eq_map,range_subtype] using hh
  have hDmn : ¬ D.map H.subtype ≤ twoCoreIn H :=
    fun hn => hDN ((map_le_map_iff_of_injective H.subtype_injective).mp hn)
  have hDA : D.map H.subtype ≤ A ⊔ conjugateSpan H V := by
    have hd : D ≤ A₀ ⊔ U :=
      sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
    have hh := map_mono (f := H.subtype) hd
    simpa only [Subgroup.map_sup,A₀,U,map_subgroupOf_eq_of_le hA.1.1,
      map_subgroupOf_eq_of_le ((span_le_right_core d hV).trans (twoCore_le H))] using hh
  have hDAq : offenderImage H (D.map H.subtype) ≤ offenderImage H A :=
    (offenderImage_le_iff hDm.1 hA.1.1).mpr
      (hDA.trans (sup_le_sup_left (span_le_right_core d hV) A))
  have heq : offenderImage H (D.map H.subtype) = offenderImage H A :=
    le_antisymm hDAq (hA.2.2 _ hDm hDmn hDAq)
  have hDel : D.map H.subtype ∈ delta H := by
    refine ⟨hDm,hDmn,?_⟩
    intro B hB hBn hBD
    rw [heq] at hBD ⊢
    exact hA.2.2 B hB hBn hBD
  refine ⟨D.map H.subtype,hDel,hDA,heq,?_⟩
  have hm : (D.map H.subtype).subgroupOf H = D := by
    apply Subgroup.map_injective H.subtype_injective
    exact map_subgroupOf_eq_of_le hDm.1
  rw [hm]
  exact hDE


end CFSG.Quasithin.Chapter15.Section02
