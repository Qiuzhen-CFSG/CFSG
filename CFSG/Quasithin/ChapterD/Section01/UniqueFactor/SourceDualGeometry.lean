module
public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceChiefLayer
public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.GroupAction.Quotient
public import Theory.GroupTheory.Commutator.ConjugateGeneration
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The single-vector commutator geometry in D.1.4

Write U=⟨Vᴳ₂⟩, K=O²(G₂), Q=⟨(R∩R₂)ᴳ₂⟩ and D=C_V(K).
The genuine unique chief layer gives [V,Q]≤D; the alternative would
force U=V by nilpotent saturation, contrary to the qrc hypotheses.
The two-group T fixes a nonidentity coset vD. Since Q centralizes D,
[v,Q] is G₂-invariant. The unique chief layer then gives
[U,Q]=[v,Q]≤D≤C_V(Q). Thus the original Q acts quadratically.
The later size comparison and dual-offender conclusion remain separate.
Source: Aschbacher–Smith, D.1.4, printed pp.175–176.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterD.UniqueFactor
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem coreClosure_commutator_centralizes_residual
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    ⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ ≤
      centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
  let U := conjugateSpan G₂ V
  let Q := intersectionClosure G₁ G₂
  have hUQ : U ≤ Q := span_le_intersectionClosure d hV
  have hQG : Q ≤ G₂ := intersectionClosure_le_right_core.trans (twoCore_le G₂)
  let := d.finite_right
  let : Finite Q := Finite.of_injective (inclusion hQG) (inclusion_injective hQG)
  have hpQ : IsPGroup 2 Q := (isPGroup_pCoreIn 2 G₂).to_le intersectionClosure_le_right_core
  have hQV : Q ≤ normalizer (V : Set G) :=
    ((intersectionClosure_le_right_core.trans (right_core_le_sylow d)).trans
      (sylow_le_left d)).trans d.module_normalized
  have hXU : ⁅U, Q⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp
    (hQG.trans (conjugateSpan_normalized G₂ V))
  have hn : G₂ ≤ normalizer (⁅U, Q⁆ : Subgroup G) := by
    dsimp only [U, Q, intersectionClosure]
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (conjugateSpan_normalized G₂ V hg),
      mem_normalizer_iff_map_conj_eq.mp (conjugateSpan_normalized G₂
        (twoCoreIn G₁ ⊓ twoCoreIn G₂) hg)]
  rcases (source_chiefLayerGeometry d hV hu).normal_subgroup_dichotomy ⁅U, Q⁆ hXU hn with hz | hle
  · exact commutator_eq_bot_iff_le_centralizer.mp hz
  · have hcover : U ≤ V ⊔ ⁅U, Q⁆ := by
      calc
        U = ⁅U, (pResidual 2 G₂).map G₂.subtype⁆ ⊔ V := span_eq_residual_commutator_sup d hV
        _ ≤ ⁅U, Q⁆ ⊔ V := sup_le_sup_right hle V
        _ = V ⊔ ⁅U, Q⁆ := sup_comm _ _
    have hUV : U ≤ V := le_of_le_sup_commutator_of_isNilpotent Q U V Q hpQ.isNilpotent
      hUQ ((le_conjugateSpan G₂ V).trans hUQ) le_rfl hQV hcover
    have he : U = V := le_antisymm hUV (le_conjugateSpan G₂ V)
    have hnormal : G₂ ≤ normalizer (V : Set G) := he ▸ conjugateSpan_normalized G₂ V
    exact (d.module_not_normalized_right (module_ne_bot hu) hnormal).elim

theorem seed_coreClosure_commutator_le_fixed
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    ⁅V, intersectionClosure G₁ G₂⁆ ≤
      V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
  refine le_inf ?_ ((commutator_mono (le_conjugateSpan G₂ V) le_rfl).trans
    (coreClosure_commutator_centralizes_residual d hV hu))
  exact le_normalizer_iff_commutator_le_left.mp
    (((intersectionClosure_le_right_core.trans (right_core_le_sylow d)).trans
      (sylow_le_left d)).trans d.module_normalized)

private theorem residual_sup_sylow (d : QRCConfiguration G₁ G₂ T V) :
    (pResidual 2 G₂).map G₂.subtype ⊔ T = G₂ := by
  let := d.finite_right
  obtain ⟨S, hS⟩ := d.sylow_right
  have h := congrArg (map G₂.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, hS, ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

theorem seed_residual_fixed_normalized (d : QRCConfiguration G₁ G₂ T V) :
    G₂ ≤ normalizer ((V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) : Subgroup G) : Set G) := by
  let K := (pResidual 2 G₂).map G₂.subtype
  let D := V ⊓ centralizer (K : Set G)
  have hKn : G₂ ≤ normalizer (K : Set G) := by
    have hn := (pResidual 2 G₂).le_normalizer_map G₂.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
    exact hn
  have hTn : T ≤ normalizer (D : Set G) :=
    (le_inf ((sylow_le_left d).trans d.module_normalized)
      (((sylow_le_right d).trans hKn).trans (normalizer_le_normalizer_centralizer K))).trans
        inf_normalizer_le_normalizer_inf
  have hKnD : K ≤ normalizer (D : Set G) :=
    (le_centralizer_iff.mp (show D ≤ centralizer (K : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer (D : Set G))
  exact (residual_sup_sylow d).symm.le.trans (sup_le hKnD hTn)

theorem coreClosure_centralizes_seed_fixed (d : QRCConfiguration G₁ G₂ T V) :
    intersectionClosure G₁ G₂ ≤
      centralizer ((V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) : Subgroup G) : Set G) := by
  apply conjugateSpan_le
  · exact (inf_le_left.trans (show twoCoreIn G₁ ≤ centralizer (V : Set G) from
      d.core_eq_centralizer ▸ inf_le_right)).trans (centralizer_le inf_le_left)
  · exact (seed_residual_fixed_normalized d).trans (normalizer_le_normalizer_centralizer _)

theorem seed_residual_fixed_lt (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) :
    V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) < V := by
  refine lt_of_le_of_ne inf_le_left ?_
  intro he
  apply d.module_not_normalized_right hne
  exact he ▸ seed_residual_fixed_normalized d

open scoped IsMulCommutative commutatorElement

private theorem sup_commutator_of_le (A B Q : Subgroup G) (hAQ : A ≤ Q) (hBQ : B ≤ Q) :
    ⁅A ⊔ B, Q⁆ = ⁅A,Q⁆ ⊔ ⁅B,Q⁆ := by
  have h := commutator_iSup_of_le (fun b : Bool => if b then A else B) Q
    (by intro b; cases b <;> assumption)
  simpa only [iSup_bool_eq, Bool.false_eq_true, ↓reduceIte, sup_comm] using h

theorem fixed_coset_commutator_normalized (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) (hu : HasUniqueNoncentralChiefFactor G₂ V)
    {v : G} (hv : v ∈ V)
    (hfixed : ∀ t ∈ T, ⁅t,v⁆ ∈ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G)) :
    G₂ ≤ normalizer ((⁅zpowers v, intersectionClosure G₁ G₂⁆ : Subgroup G) : Set G) := by
  let Q := intersectionClosure G₁ G₂
  let K := (pResidual 2 G₂).map G₂.subtype
  let D := V ⊓ centralizer (K : Set G)
  let A := zpowers v ⊔ D
  have hVQ : V ≤ Q := (le_conjugateSpan G₂ V).trans (span_le_intersectionClosure d hV)
  have hvQ : zpowers v ≤ Q := (zpowers_le.mpr hv).trans hVQ
  have hDQ : D ≤ Q := inf_le_left.trans hVQ
  have hDQc : ⁅D,Q⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (coreClosure_centralizes_seed_fixed d))
  have hAC : ⁅A,Q⁆ = ⁅zpowers v,Q⁆ := by
    rw [sup_commutator_of_le _ _ _ hvQ hDQ, hDQc, sup_bot_eq]
  have hTnA : T ≤ normalizer (A : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht a ha
    have hm : A.map (MulAut.conj t).toMonoidHom ≤ A := by
      change (zpowers v ⊔ D).map _ ≤ _
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · apply zpowers_le.mpr
        have hd := hfixed t ht
        have he : (MulAut.conj t) v = ⁅t,v⁆ * v := by
          simp only [MulAut.conj_apply, commutatorElement_def]; group
        change (MulAut.conj t) v ∈ A
        rw [he]
        exact A.mul_mem (mem_sup_right hd) (mem_sup_left (mem_zpowers v))
      · have hd : D.map (MulAut.conj t).toMonoidHom = D :=
          mem_normalizer_iff_map_conj_eq.mp
            (seed_residual_fixed_normalized d ((sylow_le_right d) ht))
        exact hd.le.trans le_sup_right
    exact hm (mem_map_of_mem _ ha)
  have hTnC : T ≤ normalizer ((⁅zpowers v,Q⁆ : Subgroup G) : Set G) := by
    rw [← hAC]
    intro t ht
    have hq : Q.map (MulAut.conj t).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp
        (conjugateSpan_normalized G₂ (twoCoreIn G₁ ⊓ twoCoreIn G₂) ((sylow_le_right d) ht))
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hTnA ht)]
    change ⁅A, Q.map (MulAut.conj t).toMonoidHom⁆ = _
    rw [hq]
  have hCD : ⁅zpowers v,Q⁆ ≤ D :=
    (commutator_mono (zpowers_le.mpr hv) le_rfl).trans
      (seed_coreClosure_commutator_le_fixed d hV hu)
  have hKnC : K ≤ normalizer ((⁅zpowers v,Q⁆ : Subgroup G) : Set G) :=
    (le_centralizer_iff.mp (hCD.trans inf_le_right)).trans (centralizer_le_normalizer _)
  exact (residual_sup_sylow d).symm.le.trans (sup_le hKnC hTnC)

theorem exists_seed_fixed_coset (d : QRCConfiguration G₁ G₂ T V) (hne : V ≠ ⊥) :
    ∃ v ∈ V, v ∉ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) ∧
      ∀ t ∈ T, ⁅t, v⁆ ∈ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) := by
  classical
  let := d.finite_left
  let : Finite V := Finite.of_injective (inclusion d.module_le) (inclusion_injective d.module_le)
  let : IsElementaryAbelian 2 V := d.module_elementary
  let D := V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G)
  let D0 := D.subgroupOf V
  let _ : MulDistribMulAction T V := MulDistribMulAction.compHom V
    (actionHom T V ((sylow_le_left d).trans d.module_normalized))
  have hDinv : IsInvariant T V D0 := by
    constructor
    intro t v
    change (v : G) ∈ D ↔ (t : G) * (v : G) * (t : G)⁻¹ ∈ D
    exact mem_normalizer_iff.mp (seed_residual_fixed_normalized d ((sylow_le_right d) t.property)) v
  let _ : MulDistribMulAction T (V ⧸ D0) := quotientMulDistribMulAction D0 hDinv
  have hquotient : Nat.card (V ⧸ D0) ≠ 1 := by
    intro hone
    have htop : D0 = ⊤ := index_eq_one.mp (by rw [index_eq_card]; exact hone)
    have hVD : V ≤ D := by
      intro v hv
      have hm : (⟨v,hv⟩ : V) ∈ D0 := by rw [htop]; trivial
      exact hm
    exact (not_le_of_gt (seed_residual_fixed_lt d hne)) hVD
  have hdiv : 2 ∣ Nat.card (V ⧸ D0) :=
    ((IsElementaryAbelian.isPGroup 2 V).to_quotient D0).card_eq_or_dvd.resolve_left hquotient
  have hTp : IsPGroup 2 T := by
    obtain ⟨S, hS⟩ := d.sylow_left
    exact hS ▸ S.isPGroup'.map G₁.subtype
  have hone : (1 : V ⧸ D0) ∈ MulAction.fixedPoints T (V ⧸ D0) := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨point, hpoint, hpointne⟩ :=
    hTp.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := V ⧸ D0) hdiv hone
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective D0 point
  refine ⟨v, v.property, ?_, ?_⟩
  · intro hv
    exact hpointne ((QuotientGroup.eq_one_iff v).mpr hv).symm
  · intro t ht
    have he := (MulAction.mem_fixedPoints.mp hpoint) (⟨t,ht⟩ : T)
    change ((actionHom T V ((sylow_le_left d).trans d.module_normalized) ⟨t,ht⟩ v : V) : V ⧸ D0) = v at he
    have hm := QuotientGroup.eq_iff_div_mem.mp he
    change t * (v : G) * t⁻¹ / (v : G) ∈ D at hm
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm

theorem fixed_coset_generates_coreClosure_commutator
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) {v : G} (hv : v ∈ V)
    (hne : v ∉ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G))
    (hfixed : ∀ t ∈ T, ⁅t,v⁆ ∈ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G)) :
    ⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ =
      ⁅zpowers v, intersectionClosure G₁ G₂⁆ := by
  let U := conjugateSpan G₂ V
  let Q := intersectionClosure G₁ G₂
  let K := (pResidual 2 G₂).map G₂.subtype
  let B := twoCoreIn G₁ ⊓ twoCoreIn G₂
  let Z := conjugateSpan G₂ (zpowers v)
  let C := ⁅zpowers v,Q⁆
  have hUQ : U ≤ Q := span_le_intersectionClosure d hV
  have hQH : Q ≤ G₂ := intersectionClosure_le_right_core.trans (twoCore_le G₂)
  have hZU : Z ≤ U := conjugateSpan_le _ _ _
    ((zpowers_le.mpr hv).trans (le_conjugateSpan G₂ V)) (conjugateSpan_normalized G₂ V)
  have hHC : G₂ ≤ normalizer (C : Set G) := fixed_coset_commutator_normalized d hV hu hv hfixed
  have hZQ : ⁅Z,Q⁆ = C := by
    have he := commutator_iSup_conjugates (zpowers v) G₂ Q
      ((zpowers_le.mpr hv).trans ((le_conjugateSpan G₂ V).trans hUQ))
      (conjugateSpan_normalized G₂ B)
    exact he.trans (conjugateSpan_eq_of_normalized G₂ C hHC)
  have hIK : ⁅U,K⁆ ≤ Z := by
    rcases (source_chiefLayerGeometry d hV hu).normal_subgroup_dichotomy Z hZU
      (conjugateSpan_normalized G₂ (zpowers v)) with hz | hi
    · exact (hne ⟨hv, (commutator_eq_bot_iff_le_centralizer.mp hz)
        ((le_conjugateSpan G₂ (zpowers v)) (mem_zpowers v))⟩).elim
    · exact hi
  have hUZV : U ≤ Z ⊔ V := by
    calc
      U = ⁅U,K⁆ ⊔ V := span_eq_residual_commutator_sup d hV
      _ ≤ Z ⊔ V := sup_le_sup_right hIK V
  have hVB : ⁅V,B⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (inf_le_left.trans
      (show twoCoreIn G₁ ≤ centralizer (V : Set G) from d.core_eq_centralizer ▸ inf_le_right)))
  have hUB : ⁅U,B⁆ ≤ C :=
    (commutator_mono hUZV le_rfl).trans
      (commutator_sup_le_of_relative_normal G₂ Z V B C hHC
        (hZU.trans (hUQ.trans hQH))
        ((le_conjugateSpan G₂ V).trans (hUQ.trans hQH))
        ((commutator_mono le_rfl (le_conjugateSpan G₂ B)).trans hZQ.le)
        (hVB.le.trans bot_le))
  apply le_antisymm
  · rw [commutator_comm]
    change ⁅⨆ g : G₂, B.map (MulAut.conj (g : G)).toMonoidHom, U⁆ ≤ C
    apply commutator_iSup_le_of_relative_normal G₂ U C _ hHC
    · intro g
      exact (map_mono (show B ≤ G₂ from inf_le_right.trans (twoCore_le G₂))).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp (G₂.le_normalizer g.property))
    · intro g
      have hUm : U.map (MulAut.conj (g : G)).toMonoidHom = U :=
        mem_normalizer_iff_map_conj_eq.mp (conjugateSpan_normalized G₂ V g.property)
      have hCm : C.map (MulAut.conj (g : G)).toMonoidHom = C :=
        mem_normalizer_iff_map_conj_eq.mp (hHC g.property)
      have hm := map_mono (f := (MulAut.conj (g : G)).toMonoidHom) hUB
      rw [map_commutator] at hm
      change ⁅U.map (MulAut.conj (g : G)).toMonoidHom,
        B.map (MulAut.conj (g : G)).toMonoidHom⁆ ≤ C.map (MulAut.conj (g : G)).toMonoidHom at hm
      rw [hUm,hCm,commutator_comm] at hm
      exact hm
  · exact commutator_mono ((zpowers_le.mpr hv).trans (le_conjugateSpan G₂ V)) le_rfl

theorem source_coreClosure_commutator_geometry
    (d : QRCConfiguration G₁ G₂ T V) (hV : V ≤ twoCoreIn G₂)
    (hu : HasUniqueNoncentralChiefFactor G₂ V) :
    ∃ v ∈ V,
      v ∉ V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) ∧
      ⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ =
        ⁅zpowers v, intersectionClosure G₁ G₂⁆ ∧
      ⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ ≤
        V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) ∧
      ⁅⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆,
        intersectionClosure G₁ G₂⁆ = ⊥ := by
  obtain ⟨v,hv,hne,hfixed⟩ := exists_seed_fixed_coset d (module_ne_bot hu)
  have he := fixed_coset_generates_coreClosure_commutator d hV hu hv hne hfixed
  have hc : ⁅conjugateSpan G₂ V, intersectionClosure G₁ G₂⁆ ≤
      V ⊓ centralizer ((pResidual 2 G₂).map G₂.subtype : Set G) :=
    he.le.trans ((commutator_mono (zpowers_le.mpr hv) le_rfl).trans
      (seed_coreClosure_commutator_le_fixed d hV hu))
  refine ⟨v,hv,hne,he,hc,commutator_eq_bot_iff_le_centralizer.mpr ?_⟩
  exact hc.trans (le_centralizer_iff.mp (coreClosure_centralizes_seed_fixed d))

end CFSG.Quasithin.ChapterD.UniqueFactor
