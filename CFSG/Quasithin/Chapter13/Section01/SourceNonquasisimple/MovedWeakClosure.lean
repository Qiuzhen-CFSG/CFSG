module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.FourGroup
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.ReducedModule
public import Theory.GroupTheory.Commutator.PerfectLayerLift
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo
public import Theory.GroupTheory.PerfectSmallTwoAction
public import Theory.ElementaryAbelian.FixedOrderGeneration
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# Both first weak closures for the original moved module

Let U=[R₂(N_G(L)),L] for a faithful maximal nonquasisimple local component.
Perfectness gives [U,L]=U, and the small normal-action bound gives |U|≥8.
Assume the original radical centralization and TI conclusions.

For a conjugate actor A of index at most two, choose a four-subgroup B≤A.
The odd Frattini-plane obstruction gives b≠1 in B acting trivially on
L/O∞(L). Hence C_U(b) is L-invariant. The TI-pair equality of the mutual
normalizer orders gives |U:C_U(b)|≤2. Every automorphism of that quotient
is trivial, so [U,L]≤C_U(b); full movement makes b fix U. The TI-pair
commutation theorem now makes all of A centralize U.

This proves W₀ and W₁ centralize U and w(T,U)>1 for every source module
branch, including the reducible branches. TI also gives r(G,U)>1. The
actual consumer discharges movement, size and all normalizer premises;
only13.1.4(5) and13.1.13 remain explicit. No irreducibility or module
classification is needed for this step of13.1.14.

Source: Aschbacher--Smith,13.1.8(2) and13.1.14(1--2), printed pp.869,875--876;
the mutual-normalizer calculation is I.6.2(1), printed pp.424--425.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

/-- Perfectness makes the original moved subgroup stable under a second
commutator, and its nontrivial two-group action gives order at least eight. -/
theorem normalizerMoved_commutator_and_card
    {T : Sylow 2 G} {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hne : normalizerMoved L ≠ ⊥) :
    ⁅normalizerMoved L,L⁆ = normalizerMoved L ∧ 8 ≤ Nat.card (normalizerMoved L) := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let V := reducedTwoSubgroup M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let e : A ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let := Chapter1.mem_L_isPerfect hL
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have he : ⁅V,A⁆.map M.subtype = normalizerMoved L := by
    rw [map_commutator,map_subgroupOf_eq_of_le L.le_normalizer]
    rw [normalizerMoved_eq]
  have hi : ⁅⁅V,A⁆,A⁆ = ⁅V,A⁆ := by
    apply le_antisymm (commutator_mono (commutator_le_left V A) le_rfl)
    exact commutator_le_of_iterated_le V A ⁅⁅V,A⁆,A⁆ le_rfl
  constructor
  · have hi := congrArg (fun H : Subgroup M => H.map M.subtype) hi
    rwa [map_commutator,he,map_subgroupOf_eq_of_le L.le_normalizer] at hi
  · have hv : IsPGroup 2 V := isPReduced_reducedPSubgroup.elementary.isPGroup
    have hn : ⁅V,A⁆ ≠ ⊥ := by
      intro hb
      apply hne
      rw [←he,hb,Subgroup.map_bot]
    have hc := commutator_card_ge_eight_of_isPerfect A V hv hn
    have hecard : Nat.card (⁅V,A⁆.map M.subtype) = Nat.card (⁅V,A⁆ : Subgroup M) :=
      card_map_of_injective M.subtype_injective
    rwa [←hecard,he] at hc

/-- A conjugate actor of index at most two centralizes a fully moved TI
module. No irreducibility or classification of the module is required. -/
theorem conjugate_actor_centralizes_of_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U A : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (g : G) (hAg : A ≤ U.map (MulAut.conj g).toMonoidHom)
    (hAU : A ≤ normalizer (U : Set G))
    (hAL : A ≤ normalizer (L : Set G))
    (hindex : A.relIndex (U.map (MulAut.conj g).toMonoidHom) ≤ 2) :
    A ≤ centralizer (U : Set G) := by
  let V := U.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAg
  have hcard : Nat.card V = Nat.card U := card_map_of_injective (MulAut.conj g).injective
  have hA : 4 ≤ Nat.card A := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le hAg
    rw [relIndex_bot_left,relIndex_bot_left,hcard] at hc
    have hb := Nat.mul_le_mul_left (Nat.card A) hindex
    rw [hc] at hb
    omega
  by_contra hnon
  have hd : Disjoint V U := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · apply (hnon ?_).elim
      rw [he] at hAg
      exact hAg.trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
    · exact hd
  obtain ⟨B,hBA,hB,hcardB,_⟩ := IsElementaryAbelian.exists_two_power_subgroup_mem A
    (n := 2) (by decide) hA 1 A.one_mem
  let := hB
  have hBL := hBA.trans hAL
  have hBU := hBA.trans hAU
  let ρ := L.normalizerMonoidHom.comp (inclusion hBL)
  let σ := U.normalizerMonoidHom.comp (inclusion hBU)
  let τ := U.normalizerMonoidHom.comp (inclusion hLU)
  have hW : solvableRadical L ≤ τ.ker := by
    intro l hl
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro u
    apply Subtype.ext
    change (l : G) * (u : G) * (l : G)⁻¹ = (u : G)
    have hc := mem_centralizer_iff.mp (hRad (mem_map_of_mem L.subtype hl)) u u.property
    change (u : G) * (l : G) = (l : G) * (u : G) at hc
    rw [← hc,mul_inv_cancel_right]
  have he (b : B) (l : L) (u : U) : σ b (τ l u) = τ (ρ b l) (σ b u) := by
    apply Subtype.ext
    change (b : G) * ((l : G) * (u : G) * (l : G)⁻¹) * (b : G)⁻¹ =
      ((b : G) * (l : G) * (b : G)⁻¹) *
        ((b : G) * (u : G) * (b : G)⁻¹) *
          ((b : G) * (l : G) * (b : G)⁻¹)⁻¹
    group
  let q := (quotientAut (solvableRadical L)).comp ρ
  have hk : q.ker ≠ ⊥ := by
    intro hk
    exact normalizer_four_group_action_not_injective hG T hL hn
      (by simpa using hcardB) hBL ((MonoidHom.ker_eq_bot_iff q).mp hk)
  obtain ⟨b,hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
  have hb1 : (b : B) ≠ 1 := fun he => hb (Subtype.ext he)
  have hbG : ((b : B) : G) ≠ 1 := fun he => hb1 (Subtype.ext he)
  let φ := QuotientGroup.lift (solvableRadical L) τ hW
  have hs (l : L) : τ (ρ b l) = τ l := by
    have hh := DFunLike.congr_fun (MonoidHom.mem_ker.mp b.property)
      (QuotientGroup.mk' (solvableRadical L) l)
    change quotientAut (solvableRadical L) (ρ b)
      (QuotientGroup.mk' (solvableRadical L) l) =
        QuotientGroup.mk' (solvableRadical L) l at hh
    rw [quotientAut_apply_mk] at hh
    exact congrArg φ hh
  have hcommute (l : L) (u : U) : σ b (τ l u) = τ l (σ b u) := by rw [he,hs]
  let C := U ⊓ centralizer ({((b : B) : G)} : Set G)
  have hLC : L ≤ normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl u hu
    have huf : σ b ⟨u,hu.1⟩ = (⟨u,hu.1⟩ : U) := by
      apply Subtype.ext
      change ((b : B) : G) * u * ((b : B) : G)⁻¹ = u
      have hh := (mem_centralizer_singleton_iff.mp hu.2).symm
      rw [hh,mul_inv_cancel_right]
    have hcf := hcommute ⟨l,hl⟩ ⟨u,hu.1⟩
    rw [huf] at hcf
    have hcf' := congrArg Subtype.val hcf
    change ((b : B) : G) * (l*u*l⁻¹) * ((b : B) : G)⁻¹ = l*u*l⁻¹ at hcf'
    exact ⟨(mem_normalizer_iff.mp (hLU hl) u).mp hu.1,
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hcf').symm⟩
  have hCeq : C = U ⊓ normalizer (V : Set G) :=
    (ti_pair_opposite_normalizer_eq_centralizer V U hd (hTI.map_equiv (MulAut.conj g))
      (hAg (hBA (b : B).property)) (hBU (b : B).property) hbG).symm
  have hcC : Nat.card C = Nat.card (V ⊓ normalizer (U : Set G) : Subgroup G) := by
    rw [hCeq]
    exact ti_pair_mutual_normalizers_card_eq U V hd.symm hTI
      (hTI.map_equiv (MulAut.conj g)) hcard.symm
  have hci : C.relIndex U ≤ 2 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) C U bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hc
    have haC : Nat.card A ≤ Nat.card C := by
      rw [hcC]
      exact card_le_of_le (le_inf hAg hAU)
    have ha := relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le hAg
    rw [relIndex_bot_left,relIndex_bot_left,hcard] at ha
    have hb := Nat.mul_le_mul_left (Nat.card A) hindex
    rw [ha] at hb
    have hp : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hUC : U ≤ C := by
    have hp : 0 < C.relIndex U := Nat.pos_of_ne_zero index_ne_zero_of_finite
    have hi : C.relIndex U = 1 ∨ C.relIndex U = 2 := by omega
    rcases hi with hi | hi
    · exact relIndex_eq_one.mp hi
    · rw [←hmoved]
      exact commutator_le_of_normalized_index_two U C L inf_le_left hi hLU hLC
  have hbC : ((b : B) : G) ∈ centralizer (U : Set G) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    exact mem_centralizer_singleton_iff.mp (hUC hu).2
  have hC : V ⊓ centralizer (U : Set G) ≠ ⊥ := by
    intro hbot
    have hx : ((b : B) : G) ∈ V ⊓ centralizer (U : Set G) :=
      ⟨hAg (hBA (b : B).property),hbC⟩
    rw [hbot] at hx
    exact hbG (mem_bot.mp hx)
  have hfull : U ⊓ normalizer (V : Set G) = U :=
    ti_pair_full_normalizer_of_centralizer_ne_bot U V hd.symm
      (hTI.map_equiv (MulAut.conj g)) hC
  have hc : U ≤ centralizer (V : Set G) :=
    ti_pair_commute_of_full_normalizer U V hd.symm hTI
      (hTI.map_equiv (MulAut.conj g)) hcard.symm hfull
  exact hnon (hAg.trans (le_centralizer_iff.mp hc))

/-- Both first weak closures centralize every fully moved TI module for an
original nonquasisimple local component, including all reducible branches. -/
theorem weakClosure_centralizes_of_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (i : ℕ) (hi : i ≤ 1) :
    ChapterE.indexedWeakClosure U (T : Subgroup G) i ≤ centralizer (U : Set G) := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAg,hindex⟩,hAT⟩
  apply conjugate_actor_centralizes_of_moved hG T hL hn hTI hLU hRad hmoved hsize g hAg
    (hAT.trans hTU) (hAT.trans hTL)
  rw [hindex]
  interval_cases i <;> norm_num

/-- The source parameter w is greater than one for a fully moved TI module,
with no extra representation hypothesis. -/
theorem globalW_gt_one_of_moved
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    1 < ChapterE.globalW U (T : Subgroup G) := by
  apply lt_of_not_ge
  intro h
  rcases Order.le_one_iff.mp h with hzero | hone
  · have he := ChapterE.globalW_attained (n := 0) hzero
    exact he (le_inf (ChapterE.indexedWeakClosure_le U (T : Subgroup G) 0)
      (weakClosure_centralizes_of_moved hG T hL hn hTI hLU hRad hmoved hsize hTU hTL 0
        (by decide)))
  · have he := ChapterE.globalW_attained (n := 1) hone
    exact he (le_inf (ChapterE.indexedWeakClosure_le U (T : Subgroup G) 1)
      (weakClosure_centralizes_of_moved hG T hL hn hTI hLU hRad hmoved hsize hTU hTL 1 le_rfl))

open Chapter12.Section02 Chapter1.Section02 in
/-- The actual U=[R₂(N_G(L)),L] satisfies the centralization and parameter conclusions
of13.1.14 once13.1.4(5) and13.1.13 supply radical centralization and TI.
All module, cardinality and normalizer inputs are discharged here. -/
theorem normalizerMoved_weakClosure_bound
    {T : Sylow 2 G} {L : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (normalizerMoved L : Set G))
    (hTI : IsTISubgroup (normalizerMoved L)) :
    (∀ i : ℕ, i ≤ 1 → ChapterE.indexedWeakClosure (normalizerMoved L) (T : Subgroup G) i ≤
      centralizer (normalizerMoved L : Set G)) ∧
      1 < ChapterE.globalW (normalizerMoved L) (T : Subgroup G) ∧
      1 < ChapterE.globalR (normalizerMoved L) := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk hG hL.1.1.2.2) hn
  obtain ⟨hU,hne,_,hN⟩ := faithful_maximal_normalizer_moved hG hL hTL
  let := hU
  obtain ⟨hmoved,hsize⟩ := normalizerMoved_commutator_and_card hL.1.1 hne
  have hLU : L ≤ normalizer (normalizerMoved L : Set G) := by rw [hN];exact L.le_normalizer
  have hTU : (T : Subgroup G) ≤ normalizer (normalizerMoved L : Set G) := by rw [hN];exact hTL
  have hr : (3 : ℕ∞) ≤ ChapterE.globalR (normalizerMoved L) := by
    apply le_iInf
    intro D
    apply le_iInf
    rintro ⟨hD,hescape⟩
    have hbot : D = ⊥ := by
      by_contra hbot
      obtain ⟨d,hd⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
      have hd1 : (d : G) ≠ 1 := fun he => hd (Subtype.ext he)
      apply hescape
      exact (centralizer_le (show ({(d : G)} : Set G) ⊆ D from
        Set.singleton_subset_iff.mpr d.property)).trans
        (hTI.centralizer_le_normalizer (hD d.property) hd1)
    subst D
    change (3 : ℕ∞) ≤ (Nat.log 2 ((⊥ : Subgroup G).relIndex (normalizerMoved L)) : ℕ∞)
    rw [relIndex_bot_left]
    exact_mod_cast (Nat.le_log_of_pow_le (by decide : 1 < 2) hsize)
  exact ⟨fun i hi => weakClosure_centralizes_of_moved hG T hL.1.1 hn hTI hLU hRad hmoved hsize
      hTU hTL i hi,
    globalW_gt_one_of_moved hG T hL.1.1 hn hTI hLU hRad hmoved hsize hTU hTL,
    lt_of_lt_of_le (by decide : (1 : ℕ∞) < 3) hr⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
