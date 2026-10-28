module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairGeometry
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairIndex
public import Theory.GroupTheory.ElementaryThompsonFourFamilySource
/-!
# Thompson stability for the original paired cubic blocks

The actual two cubic actions give the four-family geometry and identify the
module stabilizer with Baum(R), of index two in R. The original core and its
conjugate form the R-invariant pair. Counting its normalizer inside the given
index-two extension supplies the generic four-family stability argument.
The same geometry identifies the pointwise family kernel in any overgroup
with the original core-normalizer control.

Source: Aschbacher–Smith C.6.1 case (beta), paired A₃ branch, printed p.165.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

omit [Finite G] in
private theorem count (Q A : Subgroup G) :
    Nat.card ↥(Q ⊓ A) * Q.relIndex A = Nat.card A := by
  simpa only [relIndex_bot_left,inf_relIndex_right] using
    relIndex_mul_relIndex (⊥ : Subgroup G) (Q ⊓ A) A bot_le inf_le_right

theorem cubic_pair_thompson_stable_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    elementaryAbelianMaxJ M = elementaryAbelianMaxJ R := by
  obtain ⟨P,P',hf,hg,hn⟩ := cubic_pair_geometry_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc
  have hs := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hidx := (cubic_pair_index_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc).1
  let Q := H.pCoreIn 2
  let W := Q.map (MulAut.conj x⁻¹).toMonoidHom
  have hinv : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {Q,W} := hs.2.2.2.2.2.1
  have hRQ : R ≤ normalizer (Q : Set G) := c.R_le_H.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hmove : W ≠ Q := by
    intro he
    have hU : sourceModule K ≤ Q := by
      let := h.elementary
      have hUC : sourceModule K ≤ centralizer (sourceModule K ⊔ sourceModule L : Subgroup G) :=
        le_centralizer_iff.mpr (sup_le (le_centralizer (RankOne.U K))
          ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))))
      exact (le_inf (h.module_le.trans inf_le_left) hUC).trans hfull.le
    have hQC : Q ≤ centralizer (sourceModule K : Set G) := hfull.ge.trans
      (inf_le_right.trans (centralizer_le (show sourceModule K ≤ sourceModule K ⊔ sourceModule L from le_sup_left)))
    exact hnc (((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hU).trans_eq he).trans hQC)
  have hip := normalizer_relIndex_eq_two_of_pair M Q W
    (fun a ha => Theory.GroupTheory.normalizer_preserves_invariant_maxFamily_pair R Q W hinv (c.R_normal ha))
    x⁻¹ (M.inv_mem hx) hmove
  have hcontrol : M ⊓ normalizer (Q : Set G) = R := by
    have hr := count R M
    rw [inf_eq_left.mpr c.T_le,hi] at hr
    have hm := count (normalizer (Q : Set G)) M
    rw [hip,inf_comm (normalizer (Q : Set G)) M] at hm
    exact (eq_of_le_of_card_ge (le_inf c.T_le hRQ) (by omega)).symm
  exact thompson_stable_of_invariant_four_family M R (ChapterB.baumann R) Q W P P' hf hinv hg
    c.T_le inf_le_left hi hidx c.R_normal hn hcontrol

theorem cubic_pair_family_kernel_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (Λ : Subgroup G) (hcontrol : Λ ⊓ normalizer (H.pCoreIn 2 : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    (elementaryAbelianMaxJ R).relIndex R = 2 ∧
      ∀ g ∈ Λ,(∀ A ∈ elementaryAbelianMaxSubgroups R,g ∈ normalizer (A : Set G)) ↔
        g ∈ elementaryAbelianMaxJ R := by
  obtain ⟨P,P',hf,hg,hn⟩ := cubic_pair_geometry_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc
  have hs := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hidx := (cubic_pair_index_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc).1
  refine ⟨by simpa only [hs.1] using hidx,?_⟩
  rw [←hs.1]
  exact four_family_pointwise_kernel Λ R (ChapterB.baumann R) (H.pCoreIn 2)
    ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) P P' hf hs.2.2.2.2.2.1 hg
    inf_le_left hidx hn hcontrol
end CFSG.Quasithin.ChapterC.Section06
