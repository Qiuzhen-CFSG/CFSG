module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairAction
public import CFSG.Quasithin.ChapterC.Section06.RankOnePairSource
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CardFourAutomorphismStabilizer
/-!
# The original cubic-pair module stabilizer

An actor fixing each original module also fixes its conjugate in the regular
four-module orbit. Their common order-two line is fixed pointwise. Since the
module has order four, each induced automorphism image has order at most two.
The two centralizer indices bound the module stabilizer modulo the original
core by four, already attained by Baum(R). Hence this stabilizer is Baum(R),
and the actual exchange of the two modules gives index two in R.

Source: Aschbacher–Smith C.6.1, paired A₃ branch, printed p.165.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_index_le_two (T U I : Subgroup G)
    (hU : Nat.card U = 4) (hI : Nat.card I = 2) (hIU : I ≤ U)
    (hTU : T ≤ normalizer (U : Set G)) (hTI : T ≤ normalizer (I : Set G)) :
    (centralizer (U : Set G)).relIndex T ≤ 2 := by
  let a := U.normalizerMonoidHom.comp (inclusion hTU)
  have hk : a.ker = (centralizer (U : Set G)).subgroupOf T := by
    ext t
    change U.normalizerMonoidHom (inclusion hTU t) = 1 ↔ _
    change inclusion hTU t ∈ U.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hne : I ≠ ⊥ := by intro he; rw [he,Nat.card_unique] at hI; omega
  let : Nontrivial I := I.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨z,hz,hzne⟩ := I.exists_ne_one_of_nontrivial
  have hzU : (⟨z,hIU hz⟩ : U) ≠ 1 := fun he => hzne (congrArg Subtype.val he)
  have hc := card_mulAut_subgroup_le_two_of_fixed_point hU ⟨z,hIU hz⟩ hzU a.range (by
    rintro _ ⟨t,rfl⟩
    apply Subtype.ext
    change (t : G) * z * (t : G)⁻¹ = z
    have htC := normalizer_le_centralizer_of_card_two I hI (hTI t.property)
    rw [←htC z hz,mul_inv_cancel_right])
  rw [←index_ker,hk] at hc
  exact hc


open Section05.BlockAnalysis Section05.ConjugateSource
private theorem cubic_common_card {R B : Subgroup G} {E : Type*} [Field E] (k : RankOne.Setup R B E)
  (hB : IsAlternatingBlock B 3) {x : G} (hx : x ∈ normalizer (R : Set G))
    (hn : ¬ (RankOne.U B).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U B : Set G)) :
    Nat.card (RankOne.U B ⊓ (RankOne.U B).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) = 2 := by
  have he := (k.commutator_eq_fixed hx hn).1.symm.trans
    (k.commutator_eq_fixed hx hn).2
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (RankOne.U B ⊓ centralizer ((RankOne.U B).map (MulAut.conj x⁻¹).toMonoidHom : Set G))
    (RankOne.U B) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,
    RankOne.module_index_of_fixedLift k.coordinates k.fixedLift _ (k.conjugate_le hx) hn,
    k.cubic_field_card hB,k.cubic_module_card hB,he] at hm
  omega

variable {H M K L R : Subgroup G}

theorem cubic_pair_index_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    (ChapterB.baumann R).relIndex R = 2 ∧
      R ⊓ normalizer (sourceModule K : Set G) = ChapterB.baumann R := by
  let U₁ := RankOne.U K
  let U₂ := RankOne.U L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let S := ChapterB.baumann R
  let A := R ⊓ normalizer (U₁ : Set G)
  let Q := H.pCoreIn 2
  let σ := h.paired_cubic_action h' hK hL
  have hd := h.fourModuleSourceInputs hKL h'.module_le M R x hx (c.R_normal hx) hi hpair ht hnc
  have hAS : S ≤ A := le_inf inf_le_left h.coordinates.normalizes
  have hne : U₁ ≠ U₂ := by
    have hh := hd.toInputs.distinct
    exact fun he => (by decide : (0 : Fin 4) ≠ 1) (hh he)
  have hAU₂ : A ≤ normalizer (U₂ : Set G) := by
    intro a ha
    have hh : a ∈ M ⊓ normalizer (U₁ : Set G) := ⟨c.T_le ha.1,ha.2⟩
    have hn := hd.normalizers_eq 0 1
    change M ⊓ normalizer (U₁ : Set G) = M ⊓ normalizer (U₂ : Set G) at hn
    exact (hn ▸ hh).2
  have hAV₁ : A ≤ normalizer (V₁ : Set G) := by
    intro a ha
    have hh : a ∈ M ⊓ normalizer (U₁ : Set G) := ⟨c.T_le ha.1,ha.2⟩
    exact (hd.paired_normalizers ▸ hh).2
  have hAV₂ : A ≤ normalizer (V₂ : Set G) := by
    intro a ha
    have hh : a ∈ M ⊓ normalizer (U₁ : Set G) := ⟨c.T_le ha.1,ha.2⟩
    have hn := hd.normalizers_eq 0 3
    change M ⊓ normalizer (U₁ : Set G) = M ⊓ normalizer (V₂ : Set G) at hn
    exact (hn ▸ hh).2
  have h1 := centralizer_index_le_two A U₁ (U₁ ⊓ V₁) (h.cubic_module_card hK)
    (cubic_common_card h hK (c.R_normal hx) hnc) inf_le_left inf_le_right
    ((le_inf inf_le_right hAV₁).trans inf_normalizer_le_normalizer_inf)
  have h2 := centralizer_index_le_two A U₂ (U₂ ⊓ V₂) (h'.cubic_module_card hL)
    (cubic_common_card h' hL (c.R_normal hx) (RankOne.second_noncommuting hd)) inf_le_left hAU₂
    ((le_inf hAU₂ hAV₂).trans inf_normalizer_le_normalizer_inf)
  have hiQA : Q.relIndex A ≤ 4 := by
    have hh : (centralizer (U₁ : Set G) ⊓ centralizer (U₂ : Set G)).relIndex A ≤ 4 := by
      have hm := relIndex_inf_le (H := centralizer (U₁ : Set G)) (K := centralizer (U₂ : Set G)) (L := A)
      nlinarith
    have hc : centralizer (U₁ ⊔ U₂ : Subgroup G) =
        centralizer (U₁ : Set G) ⊓ centralizer (U₂ : Set G) := by
      apply le_antisymm
      · exact le_inf (centralizer_le (show U₁ ≤ U₁ ⊔ U₂ from le_sup_left))
          (centralizer_le (show U₂ ≤ U₁ ⊔ U₂ from le_sup_right))
      · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))
    rw [←hc] at hh
    change (H.pCoreIn 2).relIndex A ≤ 4
    rw [←hfull]
    have he : (R ⊓ centralizer (U₁ ⊔ U₂ : Subgroup G)) ⊓ A =
        centralizer (U₁ ⊔ U₂ : Subgroup G) ⊓ A := by
      exact le_antisymm (inf_le_inf_right _ inf_le_right)
        (le_inf (le_inf (inf_le_right.trans inf_le_left) inf_le_left) inf_le_right)
    change (R ⊓ centralizer (U₁ ⊔ U₂ : Subgroup G)).relIndex A ≤ 4
    rw [←inf_relIndex_right,he,inf_relIndex_right]
    exact hh
  have hk : σ.ker = Q.subgroupOf S := by
    rw [h.paired_cubic_kernel h' hK hL]
    ext s
    change (s : G) ∈ centralizer (U₁ ⊔ U₂ : Subgroup G) ↔ (s : G) ∈ Q
    change (s : G) ∈ centralizer (sourceModule K ⊔ sourceModule L : Subgroup G) ↔ (s : G) ∈ H.pCoreIn 2
    rw [←hfull]
    exact (and_iff_right ((show S ≤ R from inf_le_left) s.property)).symm
  have hiQS : Q.relIndex S = 4 := by
    change (Q.subgroupOf S).index = 4
    rw [←hk,index_ker,(h.paired_cubic_range h' hK hL hKL M R x hx (c.R_normal hx) hi hpair ht hnc).1]
    exact ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.actor_card
  have hQS : Q ≤ S := by
    have hf := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
    exact le_sup_left.trans hf.2.2.2.2.1.ge
  have hm := relIndex_mul_relIndex Q S A hQS hAS
  rw [hiQS] at hm
  have hiSA : S.relIndex A = 1 := by
    have hz : S.relIndex A ≠ 0 := index_ne_zero_of_finite
    omega
  have heAS : A = S := le_antisymm (relIndex_eq_one.mp hiSA) hAS
  have hn := normalizer_relIndex_eq_two_of_pair R U₁ U₂ hd.pair_zero
  obtain ⟨t,ht,hte⟩ := hd.exchange
  have hmove : U₁.map (MulAut.conj (t : G)).toMonoidHom ≠ U₁ := by
    change U₁.conjBy (t : G) ≠ U₁
    intro he
    exact hne (he.symm.trans hte)
  have hin := hn t ht hmove
  refine ⟨?_,heAS⟩
  change S.relIndex R = 2
  rw [←heAS]
  exact (inf_relIndex_left R (normalizer (U₁ : Set G))).trans hin
end CFSG.Quasithin.ChapterC.Section06
