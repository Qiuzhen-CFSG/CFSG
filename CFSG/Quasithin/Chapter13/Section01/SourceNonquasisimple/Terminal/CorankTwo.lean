module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.MovedWeakClosure
public import Theory.GroupTheory.Commutator.NormalizedPerfectSmallIndex
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard

/-!
# Corank-two weak closure for a fully moved nonquasisimple TI module

Let U be fully moved by L and have order at least eight. For a noncommuting
conjugate V whose mutual normalizer has index at most four, the involution
fixed-point bound and the TI identities force the mutual normalizer to
contain a four-group B. The original odd Frattini-plane obstruction gives
b≠1 in B acting trivially on L/O∞(L). Hence C_U(b) is L-invariant and has
index at most four. Perfectness forces L to centralize U/C_U(b), and full
movement forces b to centralize U. The TI-pair commutation theorem finishes
the contradiction. All actions here are the actual ambient conjugations.

Consequently W₂(T,U) centralizes U and w(T,U)>2. This strengthens the source
13.1.14 bound and provides a shorter route past the terminal A₅ pair analysis.
It uses no faithful-four-group-action premise or TI-pair quotient recognition.

Source: Aschbacher--Smith 13.1.7 and 13.1.14, printed pp.875--876;
the elementary TI identities are I.6.2(1),(2a), printed pp.424--425.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
open Chapter1 ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
private theorem card_le_inf_centralizer_sq_of_involution
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    {a : G} (ha : a ^ 2 = 1) (hne : a ≠ 1)
    (hN : a ∈ normalizer (U : Set G)) :
    Nat.card U ≤ Nat.card (U ⊓ centralizer ({a} : Set G) : Subgroup G)^2 := by
  have hc : (⊥ : Subgroup G).relIndex (zpowers a) = 2 := by
    rw [relIndex_bot_left,Nat.card_zpowers,orderOf_eq_prime ha hne]
  have hh := card_le_centralizer_card_sq_of_relIndex_two U ⊥ (zpowers a)
    (zpowers_le.mpr hN) (by intro u hu b hb; have hb1 : b = 1 := mem_bot.mp hb; simp [hb1]) hc
  rw [Subgroup.zpowers_eq_closure, centralizer_closure] at hh
  have he : (centralizer ({a} : Set G)).subgroupOf U =
      (U ⊓ centralizer ({a} : Set G)).subgroupOf U := by
    ext u
    simp only [mem_subgroupOf, mem_inf, u.property, true_and]
  rw [he,Nat.card_congr (subgroupOfEquivOfLe
    (show U ⊓ centralizer ({a} : Set G) ≤ U from inf_le_left)).toEquiv] at hh
  exact hh

/-- A conjugate with mutual-normalizer index at most four centralizes U. -/
theorem conjugate_centralizes_of_corank_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (hNL : normalizer (U : Set G) ≤ normalizer (L : Set G))
    (g : G)
    (hindex : (U.map (MulAut.conj g).toMonoidHom ⊓ normalizer (U : Set G)).relIndex
      (U.map (MulAut.conj g).toMonoidHom) ≤ 4) :
    U.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  let V := U.map (MulAut.conj g).toMonoidHom
  let A := V ⊓ normalizer (U : Set G)
  have hAg : A ≤ V := inf_le_left
  have hAU : A ≤ normalizer (U : Set G) := inf_le_right
  have hAL : A ≤ normalizer (L : Set G) := hAU.trans hNL
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAg
  have hcard : Nat.card V = Nat.card U := card_map_of_injective (MulAut.conj g).injective
  by_contra hnon
  have hd : Disjoint V U := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · apply (hnon ?_).elim
      rw [he]
      exact le_centralizer_iff_isMulCommutative.mpr inferInstance
    · exact hd
  have hAne : A ≠ ⊥ := by
    intro hb
    have hi := hindex
    change A.relIndex V ≤ 4 at hi
    rw [hb,relIndex_bot_left,hcard] at hi
    omega
  obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have haG : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  have ha2 : (a : G)^2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) a)
  have hfixed := card_le_inf_centralizer_sq_of_involution U ha2 haG a.property.2
  have hCeq := ti_pair_opposite_normalizer_eq_centralizer V U hd
    (hTI.map_equiv (MulAut.conj g)) a.property.1 a.property.2 haG
  rw [←hCeq,ti_pair_mutual_normalizers_card_eq U V hd.symm hTI
    (hTI.map_equiv (MulAut.conj g)) hcard.symm] at hfixed
  have hA : 4 ≤ Nat.card A := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
    have hnf : 2 ≤ n := by
      by_contra hn2
      have hp : Nat.card A ≤ 2 := by
        rw [hn]
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 1)
      change Nat.card U ≤ Nat.card A ^ 2 at hfixed
      nlinarith
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hnf
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
  have hci : C.relIndex U ≤ 4 := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) C U bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left] at hc
    have haC : Nat.card A ≤ Nat.card C := by
      rw [hcC]
    have ha := relIndex_mul_relIndex (⊥ : Subgroup G) A V bot_le hAg
    rw [relIndex_bot_left,relIndex_bot_left,hcard] at ha
    have hb := Nat.mul_le_mul_left (Nat.card A) hindex
    rw [ha] at hb
    have hp : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hUC : U ≤ C := by
    let := Chapter1.mem_L_isPerfect hL
    let : CommGroup U := IsMulCommutative.instCommGroup
    rw [←hmoved]
    exact commutator_le_of_perfect_normalized_small_index L U C hLU hLC hci
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
  exact hnon (le_centralizer_iff.mp hc)



/-- Each of the first three weak closures centralizes the original module. -/
theorem weakClosure_two_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hNL : normalizer (U : Set G) ≤ normalizer (L : Set G))
    (i : ℕ) (hi : i ≤ 2) :
    ChapterE.indexedWeakClosure U (T : Subgroup G) i ≤ centralizer (U : Set G) := by
  rw [ChapterE.weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g,hAg,hindex⟩,hAT⟩
  apply hAg.trans
  apply conjugate_centralizes_of_corank_two hG T hL hn hTI hLU hRad hmoved hsize hNL g
  apply (relIndex_le_of_le_left (le_inf hAg (hAT.trans hTU))
    index_ne_zero_of_finite).trans
  rw [hindex]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hi

/-- Full movement and the four-group obstruction give w(T,U)>2. -/
theorem globalW_gt_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L U : Subgroup G} (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    [IsElementaryAbelian 2 U] (hTI : IsTISubgroup U)
    (hLU : L ≤ normalizer (U : Set G))
    (hRad : (solvableRadical L).map L.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U,L⁆ = U) (hsize : 8 ≤ Nat.card U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hNL : normalizer (U : Set G) ≤ normalizer (L : Set G)) :
    2 < ChapterE.globalW U (T : Subgroup G) := by
  by_contra h
  have hle : ChapterE.globalW U (T : Subgroup G) ≤ 2 := le_of_not_gt h
  have hfin : ChapterE.globalW U (T : Subgroup G) ≠ ⊤ := by
    intro he
    rw [he] at hle
    exact (by simp : ¬ (⊤ : ℕ∞) ≤ 2) hle
  obtain ⟨n,he⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn2 : n ≤ 2 := by exact_mod_cast (he.symm ▸ hle)
  apply ChapterE.globalW_attained he.symm
  exact le_inf (ChapterE.indexedWeakClosure_le U (T : Subgroup G) n)
    (weakClosure_two_centralizes hG T hL hn hTI hLU hRad hmoved hsize hTU hNL n hn2)

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Terminal
