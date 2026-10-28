module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.NaturalAction
public import Theory.GroupTheory.ElementaryThompsonPairExtension
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceSingleEndgame
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.OriginalHypotheses

/-!
# The original natural-block Thompson stability in C.6.1

Let R be the source Sylow subgroup of H, normal of index two in M, and let
K=O²(H) be a natural L₂-block. The original no-common-normal hypothesis
kills the centralizer Frattini group and identifies its full module kernel
with the Baumann intersection. The actual C.5 conjugate-core family supplies
the pair swapped by M outside R. The semilinear coefficient and fixed-line
bounds then exclude every maximum elementary subgroup outside R, so
J(M)=J(R). All marked actions and cores remain the original subgroups.

Source: Aschbacher–Smith, C.6.1, printed p.165. This discharges the
Thompson-stability step used in Chapter 2, 2.4.8(1).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K R : Subgroup G}

omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

/-- Natural blocks have unchanged elementary Thompson subgroup in the
original index-two pushing-up extension. -/
theorem rankOne_thompson_stable_from_original
    (c : OriginalHypotheses H M K R R)
    {E : Type*} [Field E] (h : RankOne.Setup R K E)
    {n : ℕ} (htype : IsL2EvenBlock K n)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (RankOne.U K : Set G)) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  have hRK : R ≤ normalizer (K : Set G) := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hphi := h.frattini_eq_bot_of_index_two H M R c.T_le c.R_normal hRK hH hno
    hi x hx hnc
  have he := h.source_single_block_terminal_equalities c.R_twoGroup H M R le_rfl c.T_le
    c.R_normal hRK hH hno x hx hi hnc
  have hker : R ⊓ centralizer (RankOne.U K : Set G) ≤ RankOne.S R :=
    he.2.1.le.trans inf_le_left
  have hnatural : ∃ m, IsL2EvenBlock K m ∧ h.coordinates.IsInternal := by
    rcases h.block with hh | hA
    · exact hh
    · obtain ⟨_,_,F,_,_,hF,_,τ,⟨m⟩,_⟩ := htype
      obtain ⟨a⟩ := hA.2.2.quotient_iso
      have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 3 := by
        rw [Nat.card_congr (m.quotientIso.symm.trans a).toEquiv,nat_card_alternatingGroup]
        norm_num
      have hb := Nat.card_le_card_of_injective (Matrix.SpecialLinearGroup.upperUnipotentHom F)
        (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F)
      rw [Nat.card_congr Multiplicative.toAdd,hc,hF] at hb
      have hl : 4 ≤ 2 ^ n := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  obtain ⟨m,hm,hint⟩ := hnatural
  obtain ⟨hn,_,F,_,_,hF,_,τ,⟨model⟩,hτ⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨d⟩ := h.full_natural_model hint (h.source_sylow_block c.R_twoGroup) τ model hτ
  let Q := RankOne.Q R K
  let Q' := Q.map (MulAut.conj x⁻¹).toMonoidHom
  have hQ : Q ∈ elementaryAbelianMaxSubgroups R := by
    rw [h.sylow_maximum_family (c.R_normal hx) hnc hphi]
    exact Set.mem_insert _ _
  have hRN : R ≤ normalizer (Q : Set G) := by
    intro r hr
    exact h.block_normalizer_le_core_normalizer R R.le_normalizer ⟨hr,hRK hr⟩
  have hN : M ⊓ normalizer (Q : Set G) = R := by
    have hidx := h.core_normalizer_index M c.R_normal hx hnc hphi
    have hr := count R M
    rw [inf_eq_left.mpr c.T_le,hi] at hr
    have hm' := count (normalizer (Q : Set G)) M
    rw [hidx,inf_comm (normalizer (Q : Set G)) M] at hm'
    exact (eq_of_le_of_card_ge (le_inf c.T_le hRN) (by omega)).symm
  have hswap (a : G) (haM : a ∈ M) (haR : a ∉ R) :
      Q.map (MulAut.conj a).toMonoidHom = Q' := by
    apply (h.core_pair_preserved (c.R_normal hx) hnc hphi (c.R_normal haM)).resolve_left
    intro hfix
    exact haR (hN ▸ (show a ∈ M ⊓ normalizer (Q : Set G) from
      ⟨haM,mem_normalizer_iff_map_conj_eq.mpr hfix⟩))
  have hswap' (a : G) (haM : a ∈ M) (haR : a ∉ R) :
      Q.map (MulAut.conj a).toMonoidHom = Q' ∧ Q'.map (MulAut.conj a).toMonoidHom = Q := by
    refine ⟨hswap a haM haR,?_⟩
    have hai : a⁻¹ ∉ R := fun ha => haR (by simpa only [inv_inv] using R.inv_mem ha)
    rw [←hswap a⁻¹ (M.inv_mem haM) hai,map_map]
    have hcomp : (MulAut.conj a).toMonoidHom.comp (MulAut.conj a⁻¹).toMonoidHom = MonoidHom.id G := by
      ext g
      simp [MulAut.conj_apply,mul_assoc]
    rw [hcomp,map_id]
  let : IsElementaryAbelian 2 Q := h.core_elementary (c.R_normal hx) hnc hphi
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hQ'S : Q' ≤ RankOne.S R := (h.conjugate_core (c.R_normal hx)).le.trans inf_le_left
  have hcover (b : G) (hb : b ∈ RankOne.S R) (hb2 : b ^ 2 = 1) : b ∈ Q ∨ b ∈ Q' :=
    involution_in_pair (RankOne.S R) Q Q' (h.core_span (c.R_normal hx) hnc)
      (hQ'S.trans (inf_le_left.trans hRN))
      (fun s hs hsq => h.core_fixed_singleton (c.R_normal hx) hnc hphi s hs hsq) b hb hb2
  have hlarge : 4 * Nat.card (Q ⊓ Q' : Subgroup G) ≤ Nat.card Q := by
    have hc := h.thompson_core_intersection_card d (c.R_normal hx) hnc
    have hf : 4 ≤ Nat.card F := by
      rw [hF]
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
    change Nat.card (Q ⊓ Q' : Subgroup G) * Nat.card F = Nat.card Q at hc
    nlinarith
  exact thompson_stable_of_pair_count M R (RankOne.S R) Q Q' c.T_le inf_le_left hQ hi
    (d.elementary_card_bound hRK hker) hcover hswap'
    (h.thompson_intersection_centralizer d c.R_twoGroup hRK hker (c.R_normal hx)) hlarge
end CFSG.Quasithin.ChapterC.Section06
