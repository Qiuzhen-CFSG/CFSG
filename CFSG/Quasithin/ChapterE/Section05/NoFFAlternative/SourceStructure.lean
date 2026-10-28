module
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Defs
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Rank
public import CFSG.Quasithin.ChapterE.Section05.NoFFAlternative.Sections
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Direct structural reductions for the no-FF alternative

The rank bound on G/O₂(G) puts the ordinary Thompson subgroup of O₂(G)
inside W. The omega-centralizer identity then gives [D,O₂(G)] ≤ W.
Characteristic two and the normal two-layer fixer imply D ≤ O₂(G), and
therefore D ≤ Ω₁(Z(W)). This argument proves the needed center containment
without whole-group E-membership. It also supplies the sharp displacement
bound for an escaping maximum elementary subgroup.

Two separate results identify what the printed structural inferences require.
When F*(G/O₂(G)) is quasisimple, its equality with the residual image is
*equivalent* to the quotient above F* being a two-group. Furthermore E2
membership forces every solvable quotient to be a two-group. Neither extra
condition is asserted to follow from the hypotheses of E.5.4 here. This module
does not assert E.5.4 or promotion of residual activity to component activity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma E.5.4,
printed p.244 (PDF p.255), and the two-layer argument of E.5.1, printed p.242.
-/

open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.NoFFAlternative.SourceStructure
open ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Quotienting by the two-core leaves trivial two-core. -/
public theorem quotient_twoCore_eq_bot : pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let Q := pCore 2 G
  let π := QuotientGroup.mk' Q
  have hk : IsPGroup 2 π.ker := by
    change IsPGroup 2 (QuotientGroup.mk' Q).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hn : IsPGroup 2 ((pCore 2 (G ⧸ Q)).comap π) :=
    pCore_isPGroup.comap_of_ker_isPGroup π hk
  have hle : (pCore 2 (G ⧸ Q)).comap π ≤ Q := le_sSup ⟨inferInstance, hn⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff g).mpr (hle hx)

/-- The source quotient-rank bound controls the actual image of every elementary
subgroup, expressed using its relative index over the core intersection. -/
public theorem core_image_rank_le (A : Subgroup G) [IsElementaryAbelian 2 A]
    (j : ℕ) (hr : primeRank 2 (G ⧸ pCore 2 G) ≤ j) :
    Nat.log 2 ((A ⊓ pCore 2 G).relIndex A) ≤ j := by
  let f := QuotientGroup.mk' (pCore 2 G)
  let _ : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  have hc := (primeRank_le_iff_elementary_card_le (G ⧸ pCore 2 G)).mp hr
    (A.map f) inferInstance
  have hi : (A ⊓ pCore 2 G).relIndex A = Nat.card (A.map f) := by
    rw [inf_relIndex_left]
    simpa only [f, QuotientGroup.ker_mk'] using relIndex_ker A f
  rw [hi]
  have h := Nat.log_mono_right (b := 2) hc
  rwa [Nat.log_pow Nat.one_lt_two] at h

private theorem maxJ_core_le (P : Sylow 2 G) (A : Subgroup G) (j : ℕ)
    (hA : A ∈ thompsonFamily (P : Subgroup G) 0)
    (hj : j < twoRank (P : Subgroup G))
    (hr : Nat.log 2 ((A ⊓ pCore 2 G).relIndex A) ≤ j) :
    elementaryAbelianMaxJ (pCore 2 G) ≤ higherThompsonCore (P : Subgroup G) ⊤ j := by
  let B := A ⊓ pCore 2 G
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
    (show B ≤ A from inf_le_left)
  obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hrank := ((mem_thompsonFamily_iff_rank (P : Subgroup G) A 0).mp hA).2.2
  have hdiff := log_card_sub_log_card_eq_log_relIndex A B inf_le_left
  change Nat.log 2 (B.relIndex A) ≤ j at hr
  rw [← hdiff, hb, Nat.log_pow Nat.one_lt_two] at hr
  have hcard : 2 ^ (twoRank (P : Subgroup G) - j) ≤ Nat.card B := by
    rw [hb]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply sSup_le
  intro C hC
  let _ : IsElementaryAbelian 2 C := hC.2.1
  have hcardC := hcard.trans (hC.2.2 B inf_le_right inferInstance)
  intro x hx
  obtain ⟨F, hFC, heF, hcardF, hxF⟩ :=
    IsElementaryAbelian.exists_two_power_subgroup_mem C (by omega) hcardC x hx
  apply (le_sSup (s := {F : Subgroup G |
    F ∈ thompsonFamily (P : Subgroup G) j ∧
      F ≤ (pCore 2 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype}) ?_) hxF
  refine ⟨⟨hFC.trans (hC.1.trans (pCore_isPGroup.le_sylow_of_normal P)),
    heF, hj.le, hcardF⟩, ?_⟩
  rw [top_core_map]
  exact hFC.trans hC.1

/-- Characteristic two and the quotient-rank bound prove the center containment
needed by E.5.4, without any E-member or residual-image premise. -/
public theorem center_le_core_center (P : Sylow 2 G) (A : Subgroup G) (j : ℕ)
    (hA : A ∈ thompsonFamily (P : Subgroup G) 0)
    (hchar : generalizedFitting G = pCore 2 G)
    (hr : primeRank 2 (G ⧸ pCore 2 G) ≤ j) :
    higherThompsonCenter (P : Subgroup G) j ≤
      omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j) := by
  by_cases hdeg : twoRank (P : Subgroup G) ≤ j
  · rw [higherThompsonCenter_eq_bot_of_rank_le _ _ hdeg]
    exact bot_le
  have hj : j < twoRank (P : Subgroup G) := Nat.lt_of_not_ge hdeg
  let D := higherThompsonCenter (P : Subgroup G) j
  let W := higherThompsonCore (P : Subgroup G) ⊤ j
  let Q := pCore 2 G
  let _ : IsElementaryAbelian 2 A := hA.2.1
  have hJ : elementaryAbelianMaxJ Q ≤ W := maxJ_core_le P A j hA hj
    (core_image_rank_le A j hr)
  have hWQ : W ≤ Q := by
    simpa only [top_core_map] using higherThompsonCore_le_core (P : Subgroup G) ⊤ j
  have hQP : Q ≤ (P : Subgroup G) := pCore_isPGroup.le_sylow_of_normal P
  let _ : W.Normal := by
    apply normalizer_eq_top_iff.mp
    exact top_le_iff.mp
      ((normal_subgroupOf_iff_le_normalizer (higherThompsonCore_le _ ⊤ j)).mp
        (higherThompsonCore_normal _ ⊤ j (by simpa only [top_core_map] using hQP)))
  have hDW : D ≤ centralizer (W : Set G) :=
    (higherThompsonCenter_centralizes _ j).trans
      (centralizer_le (higherThompsonCore_le_thompsonJ _ ⊤ j))
  have hOmega : omegaOneAmbient (Q ⊓ centralizer (W : Set G)) ≤ W := by
    have h := omegaOneAmbient_mono (inf_le_inf_left Q (centralizer_le hJ))
    rw [omegaCentralizer_thompson] at h
    exact h.trans (fun x hx => hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
  have hDQW : D ⊓ Q ≤ W := by
    intro d hd
    apply hOmega
    exact (omegaOneAmbient_le_iff _ _).mp le_rfl d ⟨hd.2, hDW hd.1⟩
      ((mem_omegaOneCenterAmbient_iff _ _).mp hd.1).2.1
  have hcomm : ⁅D, Q⁆ ≤ W := by
    apply le_trans _ hDQW
    apply le_inf
    · exact le_normalizer_iff_commutator_le_left.mp (hQP.trans
        ((P : Subgroup G).le_normalizer.trans
          (normalizer_le_normalizer_higherThompsonCenter _ j)))
    · exact le_normalizer_iff_commutator_le_right.mp le_normalizer_of_normal
  have hc : pResidual 2 G ⊓ centralizer (Q : Set G) ≤ Q := by
    apply inf_le_right.trans
    change centralizer (pCore 2 G : Set G) ≤ pCore 2 G
    rw [← hchar]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  have hDQ : D ≤ Q :=
    (le_inf hDW (le_commutatorPreimage le_top hcomm)).trans
      (two_layer_le_radical Q W Q (pCore_isPGroup.to_le hWQ)
        quotient_twoCore_eq_bot hc)
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff W x).mpr
    ⟨hDQW ⟨hx, hDQ hx⟩, ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.1,
      mem_centralizer_iff.mp (hDW hx)⟩

/-- The sharp displacement bound for E = Ω₁(Z(W)), using the source quotient
rank bound directly rather than obtaining it from E-membership. -/
public theorem core_center_displacement_le_of_quotient_rank (P : Sylow 2 G)
    (A : Subgroup G) (j : ℕ) (hj : j < twoRank (P : Subgroup G))
    (hA : A ∈ thompsonFamily (P : Subgroup G) 0)
    (hr : primeRank 2 (G ⧸ pCore 2 G) ≤ j) :
    let E := omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j)
    Nat.log 2 ((E ⊓ centralizer (A : Set G)).relIndex E) ≤
      Nat.log 2 ((A ⊓ pCore 2 G).relIndex A) := by
  let W := higherThompsonCore (P : Subgroup G) ⊤ j
  let E := omegaOneCenterAmbient W
  let B := A ⊓ pCore 2 G
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian W
  have hBW : B ≤ W := by
    have h := inf_core_le_higherThompsonCore (P : Subgroup G) A ⊤ 0 j hA
      (by simpa only [Nat.zero_add] using hj)
      (by simpa only [top_core_map] using core_image_rank_le A j hr)
    simpa only [Nat.zero_add, top_core_map] using h
  have hWE : W ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mp
    intro e he
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff W e).mp he).2.2
  have hWQ : W ≤ pCore 2 G := by
    simpa only [top_core_map] using higherThompsonCore_le_core (P : Subgroup G) ⊤ j
  have hEP : E ≤ (P : Subgroup G) := by
    intro e he
    exact pCore_isPGroup.le_sylow_of_normal P
      (hWQ ((mem_omegaOneCenterAmbient_iff W e).mp he).1)
  have hb := elementary_relativeIndex_le_of_thompsonFamily (P : Subgroup G) A B E
    hA inf_le_left (le_rfl : Nat.log 2 (B.relIndex A) ≤ Nat.log 2 (B.relIndex A))
    hEP (hBW.trans hWE)
  have hBC : B ≤ centralizer (A : Set G) :=
    inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative A))
  have hi : (E ⊓ centralizer (A : Set G)).relIndex E ≤ (E ⊓ B).relIndex E :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero ((E ⊓ B).subgroupOf E).index_ne_zero_of_finite)
      (relIndex_dvd_of_le_left E (inf_le_inf_left E hBC))
  exact (Nat.log_mono_right hi).trans (by simpa only [Nat.zero_add] using hb)

/-- The residual-image equality used in the printed proof is exactly the
additional assertion that the quotient above the quasisimple F* is a two-group. -/
public theorem residual_image_eq_iff_two_group_quotient
    (hL : IsQuasisimple (generalizedFitting (G ⧸ pCore 2 G))) :
    (pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G)) =
      generalizedFitting (G ⧸ pCore 2 G) ↔
    IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ generalizedFitting (G ⧸ pCore 2 G)) := by
  rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  constructor
  · intro h
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq h)
  · intro h
    let _ : IsQuasisimple (generalizedFitting (G ⧸ pCore 2 G)) := hL
    let _ : Group.IsNilpotent
        ((G ⧸ pCore 2 G) ⧸ pResidual 2 (G ⧸ pCore 2 G)) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_antisymm (sInf_le ⟨inferInstance, h⟩)
      (le_of_isPerfect_of_solvable_quotient _ _)

/-- Every solvable quotient of an E2 member is a two-group. -/
public theorem two_group_quotient_of_top_component
    {H : Type*} [Group H] [Group.IsSolvable H]
    (P A : Subgroup G) (hc : ECaseComponent P A ⊤)
    (f : G →* H) (hf : Function.Surjective f) : IsPGroup 2 H := by
  let _ : Finite H := Finite.of_surjective f hf
  let g := f.comp (⊤ : Subgroup G).subtype
  have hg : Function.Surjective g := hf.comp Subgroup.topEquiv.surjective
  have he := congrArg (Subgroup.map g) hc.2.2.1
  rw [map_pResidual_of_surjective 2 g hg, map_solvableResidual_eq g hg,
    solvableResidual_eq_bot] at he
  exact (isPGroup_quotient_pResidual (G := H) 2).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot)

/-- The structural clause in E2 excludes every solvable quotient which is not
 a two-group, including a nontrivial odd-order abelian quotient. -/
public theorem not_top_component_of_solvable_quotient
    {H : Type*} [Group H] [Group.IsSolvable H]
    (f : G →* H) (hf : Function.Surjective f) (hH : ¬ IsPGroup 2 H)
    (P A : Subgroup G) : ¬ ECaseComponent P A ⊤ := by
  intro hc
  exact hH (two_group_quotient_of_top_component P A hc f hf)

/-- The escaping maximum subgroup supplies the center containment and the sharp
 displacement bound directly from the source hypotheses. No E-membership is
 required. The remaining source issue is residual versus component activity. -/
public theorem exists_escaping_with_center_and_displacement (P : Sylow 2 G)
    (j : ℕ) (hj : j < twoRank (P : Subgroup G))
    (hJ : ¬ (thompsonJ (P : Subgroup G) 0).Normal)
    (hchar : generalizedFitting G = pCore 2 G)
    (hr : primeRank 2 (G ⧸ pCore 2 G) ≤ j) :
    ∃ A ∈ thompsonFamily (P : Subgroup G) 0, ¬ A ≤ pCore 2 G ∧
      higherThompsonCenter (P : Subgroup G) j ≤
        omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j) ∧
      let E := omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j)
      Nat.log 2 ((E ⊓ centralizer (A : Set G)).relIndex E) ≤
        Nat.log 2 (Nat.card (A.map (QuotientGroup.mk' (pCore 2 G)))) := by
  obtain ⟨A, hA, hAQ⟩ := exists_maximum_escaping_core P hJ
  refine ⟨A, hA, hAQ, center_le_core_center P A j hA hchar hr, ?_⟩
  have hd := core_center_displacement_le_of_quotient_rank P A j hj hA hr
  rw [inf_relIndex_left, ← QuotientGroup.ker_mk' (pCore 2 G), relIndex_ker] at hd
  exact hd

end CFSG.Quasithin.ChapterE.NoFFAlternative.SourceStructure
