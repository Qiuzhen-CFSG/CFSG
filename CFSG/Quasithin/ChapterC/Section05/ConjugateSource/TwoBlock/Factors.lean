module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Product
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamilyKernel
public import Theory.GroupTheory.DisjointCommutingProjection

/-!
# Direct factors for the two-block conjugate-module argument

The fixed-space intersection shows that Fᵢ=UᵢUᵢˣ is disjoint from C_S(Kᵢ).
Its centre lies in Uᵢ. Combined with the actual four-module commutation relation,
this proves S=F₁ × F₂ × C_S(K₁K₂). The projection onto each Fᵢ has the literal
centralizer kernel needed to descend the marked deleted-permutation action.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/

public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.conjugate_factor_product
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let F := U ⊔ V
    let Q := (K ⊔ S).pCoreIn 2
    let D := S ⊓ centralizer (K : Set G)
    S = F ⊔ D ∧ Disjoint F D ∧ D ≤ centralizer (F : Set G) ∧
      F ⊓ Q = U ∧ F ⊓ centralizer (F : Set G) ≤ U := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let F := U ⊔ V
  let Q := (K ⊔ S).pCoreIn 2
  let D := S ⊓ centralizer (K : Set G)
  have hprod : Q = U ⊔ D := h.product
  have hcore : Q = S ⊓ centralizer (U : Set G) := h.core
  have hUQ : U ≤ Q := le_sup_left.trans_eq hprod.symm
  have hQS : Q ≤ S := hcore.le.trans inf_le_left
  have hUS : U ≤ S := h.module_le
  have hSx : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono hUS).trans_eq hSx
  have hFS : F ≤ S := sup_le hUS hVS
  have hSU : S ≤ normalizer (U : Set G) :=
    h.normalizes.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hVU : V ≤ normalizer (U : Set G) := hVS.trans hSU
  have hDU : D ≤ centralizer (U : Set G) :=
    inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hDV : D ≤ centralizer (V : Set G) := h.centralizer_centralizes_conjugate x hx hnc
  have hDF : D ≤ centralizer (F : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hDU) (le_centralizer_iff.mp hDV)
  have hFQ : F ⊓ Q = U := by
    apply le_antisymm
    · rintro g ⟨hg, hgQ⟩
      have hm : g ∈ (U : Set G) * (V : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left U V hVU]
        exact hg
      obtain ⟨u, hu, v, hv, rfl⟩ := hm
      have hvQ : v ∈ Q := by simpa using Q.mul_mem (Q.inv_mem (hUQ hu)) hgQ
      have hvU : v ∈ U :=
        (show V ⊓ centralizer (U : Set G) ≤ U from
          (h.conjugate_fixed_eq_intersection x hx hnc).le.trans inf_le_left)
          ⟨hv, (hcore.le hvQ).2⟩
      exact U.mul_mem hu hvU
    · exact le_inf le_sup_left hUQ
  have hFD : Disjoint F D := by
    rw [disjoint_iff_inf_le]
    have hD_Q : D ≤ Q := le_sup_right.trans_eq hprod.symm
    have hi : F ⊓ D ≤ U ⊓ D :=
      le_inf ((inf_le_inf_left F hD_Q).trans hFQ.le) inf_le_right
    exact hi.trans (alternatingModule_disjoint_of_commuting K D h.block inf_le_right).le_bot
  refine ⟨?_, hFD, hDF, hFQ, ?_⟩
  · have hs : S = V ⊔ Q := h.first_factorization x hx hnc
    change S = (U ⊔ V) ⊔ D
    rw [hs, hprod]
    ac_rfl
  · have hi : F ⊓ centralizer (F : Set G) ≤ F ⊓ Q := by
      apply le_inf inf_le_left
      rw [hcore]
      exact le_inf (inf_le_left.trans hFS)
        (inf_le_right.trans (centralizer_le (show U ≤ F from le_sup_left)))
    exact hi.trans hFQ.le

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource



namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.exists_conjugate_factor_projection
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let F := sourceModule K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    let D := S ⊓ centralizer (K : Set G)
    ∃ f : S →* F, Function.Surjective f ∧ f.ker = D.subgroupOf S ∧
      ∀ s : S, (s : G) ∈ F → (f s : G) = (s : G) := by
  have hd := h.conjugate_factor_product x hx hnc
  exact exists_projection_of_disjoint_commuting_product _ _ _ hd.1 hd.2.1
    (le_centralizer_iff.mp hd.2.2.1)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open Subgroup
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_direct_product
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let F₁ := sourceModule K ⊔ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom
    let F₂ := sourceModule L ⊔ (sourceModule L).map (MulAut.conj x⁻¹).toMonoidHom
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    S = F₁ ⊔ (F₂ ⊔ D) ∧ Disjoint F₁ (F₂ ⊔ D) ∧
      F₁ ≤ centralizer (F₂ ⊔ D : Subgroup G) ∧
      Disjoint F₂ D ∧ F₂ ≤ centralizer (D : Set G) := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let D₁ := S ⊓ centralizer (K : Set G)
  let D₂ := S ⊓ centralizer (L : Set G)
  let Q := S ⊓ centralizer (U₁ ⊔ U₂ : Subgroup G)
  have hD₁ : D ≤ D₁ := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left)))
  have hD₂ : D ≤ D₂ := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right)))
  have hU₁D₂ : U₁ ≤ D₂ := le_inf h.module_le ((map_subtype_le _).trans h'.commute)
  have hd := h.fourModuleSourceInputs h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hf₁ := h.conjugate_factor_product x hxR hnc
  have hf₂ := h'.conjugate_factor_product x hxR hd.second_noncommuting
  have hF₁F₂ : F₁ ≤ centralizer (F₂ : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (h.four_module_geometry h'.module_le M T_H x hx hxR hindex hpair ht hnc).2.2.2
  have hDF₁ : D ≤ centralizer (F₁ : Set G) := hD₁.trans hf₁.2.2.1
  have hDF₂ : D ≤ centralizer (F₂ : Set G) := hD₂.trans hf₂.2.2.1
  have hoC : F₂ ⊔ D ≤ centralizer (F₁ : Set G) :=
    sup_le (le_centralizer_iff.mp hF₁F₂) hDF₁
  have hdisj : Disjoint F₁ (F₂ ⊔ D) := by
    rw [disjoint_iff_inf_le]
    rintro z ⟨hz₁, hzo⟩
    have hzU : z ∈ U₁ := hf₁.2.2.2.2 ⟨hz₁, hoC hzo⟩
    have hzD₂ : z ∈ D₂ := hU₁D₂ hzU
    have hm : z ∈ (F₂ : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left F₂ D
        (hDF₂.trans (Subgroup.centralizer_le_normalizer _))]
      exact hzo
    obtain ⟨f, hf, d, hd, rfl⟩ := hm
    have hfD₂ : f ∈ D₂ := by simpa using D₂.mul_mem hzD₂ (D₂.inv_mem (hD₂ hd))
    have hf1 : f = 1 := (show f ∈ (⊥ : Subgroup G) from hf₂.2.1.eq_bot ▸ ⟨hf, hfD₂⟩)
    have hdF₁ : d ∈ F₁ := by
      change f * d ∈ F₁ at hz₁
      rw [hf1, one_mul] at hz₁
      exact hz₁
    have hd1 : d = 1 := (show d ∈ (⊥ : Subgroup G) from hf₁.2.1.eq_bot ▸ ⟨hdF₁, hD₁ hd⟩)
    simp only [hf1, hd1, mul_one, one_mem]
  refine ⟨?_, hdisj, le_centralizer_iff.mp hoC, hf₂.2.1.mono_right hD₂,
    le_centralizer_iff.mp hDF₂⟩
  have hc := h.two_block_factorization h' M T_H x hx hxR hindex hpair ht hnc
  have hs : S = (U₁ ⊔ U₂).map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q := hc.2.2.1
  have hq : Q = (U₁ ⊔ U₂) ⊔ D := hc.1
  change S = (U₁ ⊔ V₁) ⊔ ((U₂ ⊔ V₂) ⊔ D)
  rw [hs, hq, Subgroup.map_sup]
  dsimp only [V₁, V₂]
  ac_rfl
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource

