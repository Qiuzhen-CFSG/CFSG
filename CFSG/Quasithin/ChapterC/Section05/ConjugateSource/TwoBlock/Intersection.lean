module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Factors
public import Theory.GroupTheory.CommutingFactorIntersection

/-!
# The rank-four intersection in the paired alternating-five branch

The two conjugate factors commute and are disjoint. Each module meets its
conjugate in its commutator plane, of order four, so their product meets its
conjugate in the product of those planes. Mutual normalization identifies
this intersection with the full commutator subgroup. The conclusion keeps
the literal chosen conjugation by x⁻¹, and also records the module order 256.

Source: Aschbacher--Smith, C.5.6(2),(7)(iii), printed pp.156--159;
the intersection calculation used in 14.6.9, printed p.1027.
-/

public section
open Subgroup
variable {G : Type*} [Group G]

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_intersection
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let A := sourceModule K ⊔ sourceModule L
    let Ar := A.map (MulAut.conj x⁻¹).toMonoidHom
    A ⊓ Ar = ⁅A, Ar⁆ ∧ Nat.card (A ⊓ Ar : Subgroup G) = 16 ∧ Nat.card A = 256 := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let E₁ := U₁ ⊓ V₁
  let E₂ := U₂ ⊓ V₂
  let A := U₁ ⊔ U₂
  let V := V₁ ⊔ V₂
  have heV : A.map (MulAut.conj x⁻¹).toMonoidHom = V := Subgroup.map_sup _ _ _
  have hp := h.two_block_direct_product h' M T_H x hx hxR hindex hpair ht hnc
  have hd : Disjoint F₁ F₂ := hp.2.1.mono_right le_sup_left
  have hc : F₁ ≤ centralizer (F₂ : Set G) :=
    hp.2.2.1.trans (centralizer_le (show F₂ ≤
      F₂ ⊔ (S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)) from le_sup_left))
  have hi : A ⊓ V = E₁ ⊔ E₂ :=
    sup_inf_sup_eq_of_disjoint_commuting_factors F₁ F₂ U₁ U₂ V₁ V₂ hd hc
      le_sup_left le_sup_left le_sup_right le_sup_right
  have hnc' := (h.fourModuleSourceInputs h'.module_le M T_H x hx hxR
    hindex hpair ht hnc).second_noncommuting
  have hE₁ : ⁅U₁, V₁⁆ = U₁ ⊓ centralizer (V₁ : Set G) ∧ ⁅U₁, V₁⁆ = E₁ :=
    h.commutator_eq_fixed x hxR hnc
  have hE₂ : ⁅U₂, V₂⁆ = U₂ ⊓ centralizer (V₂ : Set G) ∧ ⁅U₂, V₂⁆ = E₂ :=
    h'.commutator_eq_fixed x hxR hnc'
  have hc₁ : Nat.card E₁ = 4 := by
    rw [← hE₁.2, hE₁.1]
    exact h.conjugate_fixed_card x hxR hnc
  have hc₂ : Nat.card E₂ = 4 := by
    rw [← hE₂.2, hE₂.1]
    exact h'.conjugate_fixed_card x hxR hnc'
  have hEc : E₂ ≤ normalizer (E₁ : Set G) :=
    ((show E₂ ≤ F₂ from inf_le_left.trans le_sup_left).trans
      ((le_centralizer_iff.mp hc).trans
        (centralizer_le (show E₁ ≤ F₁ from inf_le_left.trans le_sup_left)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hEd : Disjoint E₁ E₂ := hd.mono (inf_le_left.trans le_sup_left)
    (inf_le_left.trans le_sup_left)
  have hcard : Nat.card (A ⊓ V : Subgroup G) = 16 := by
    rw [hi, card_sup_eq_mul_of_normalizes_of_disjoint E₁ E₂ hEc hEd, hc₁, hc₂]
  have hn₁ := h.transvection_normalizes x hxR
  have hn₂ := h'.transvection_normalizes x hxR
  have hNA : S ≤ normalizer (A : Set G) :=
    ((baumann_le_transvectionRadical R).trans (le_inf hn₁.1 hn₂.1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup U₁ U₂)
  have hNV : S ≤ normalizer (V : Set G) :=
    ((baumann_le_transvectionRadical R).trans (le_inf hn₁.2.1 hn₂.2.1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup V₁ V₂)
  have hAS : A ≤ S := sup_le h.module_le h'.module_le
  have hSx : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hxR))
  have hVS : V ≤ S := heV ▸ ((map_mono hAS).trans_eq hSx)
  have hcomm : A ⊓ V = ⁅A, V⁆ := by
    apply le_antisymm
    · rw [hi]
      apply sup_le
      · rw [← hE₁.2]
        exact commutator_mono le_sup_left le_sup_left
      · rw [← hE₂.2]
        exact commutator_mono le_sup_right le_sup_right
    · exact le_inf (le_normalizer_iff_commutator_le_left.mp (hVS.trans hNA))
        (le_normalizer_iff_commutator_le_right.mp (hAS.trans hNV))
  have hAU : Nat.card A = 256 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U₁ U₂
      (((show U₂ ≤ F₂ from le_sup_left).trans
        ((le_centralizer_iff.mp hc).trans (centralizer_le (show U₁ ≤ F₁ from le_sup_left)))).trans
          (Subgroup.centralizer_le_normalizer _))
      (hd.mono le_sup_left le_sup_left), h.module_card, h'.module_card]
  change A ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom =
      ⁅A, A.map (MulAut.conj x⁻¹).toMonoidHom⁆ ∧
    Nat.card (A ⊓ A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) = 16 ∧ Nat.card A = 256
  rw [heV]
  exact ⟨hcomm, hcard, hAU⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
