module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FactorQuotient
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.QuotientBasic
public import Stellmacher.ElementaryAbelianMaxProduct

/-!
# The two natural factors become a direct product modulo D

The central intersection in each factor lies in C_S(K₁K₂). The regular
four-module action makes the two factors commute, and their remaining
intersection is also killed by D. Thus their literal images form a direct
product, with two maximum elementary choices in each factor.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G T : Type*} [Group G] [Finite G] [Group T]
variable {R K L : Subgroup G} {𝔽 𝔽' : Type*} [Field 𝔽] [Field 𝔽']

omit [Finite G] in
private theorem image_sup (f : S R →* T) (A B : Subgroup G) (hA : A ≤ S R) (hB : B ≤ S R) :
    baumannImage R f (A ⊔ B) = baumannImage R f A ⊔ baumannImage R f B := by
  rw [baumannImage, subgroupOf_sup hA hB, Subgroup.map_sup]
  rfl

omit [Finite G] in
private theorem image_commuting (f : S R →* T) (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) :
    baumannImage R f A ≤ centralizer (baumannImage R f B : Set T) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  exact (map_mul f b a).symm.trans
    ((congrArg f (Subtype.ext (hc ha b hb))).trans (map_mul f a b))

/-- The literal factors in S/D are disjoint and generate the quotient. -/
theorem Setup.two_block_quotient_product
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)).subgroupOf (S R)) :
    let A := baumannImage R f (factor K x)
    let B := baumannImage R f (factor L x)
    A ⊔ B = ⊤ ∧ Disjoint A B ∧ A ≤ centralizer (B : Set T) := by
  let D := S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let F₁ := factor K x
  let F₂ := factor L x
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hp := h.two_block_factorization h' hKL M T_H x hx hxR hindex hpair ht hnc
  have hd₁ := h.conjugate_factor_structure hxR hnc
  have hd₂ := h'.conjugate_factor_structure hxR (second_noncommuting hi)
  have hD₁ : D ≤ RankOne.D R K := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left)))
  have hD₂ : D ≤ RankOne.D R L := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right)))
  have hU₁D₂ : U K ≤ RankOne.D R L := le_inf h.module_le
    ((map_subtype_le _).trans (le_centralizer_iff.mp hKL))
  have hU₂D₁ : U L ≤ RankOne.D R K := le_inf h'.module_le ((map_subtype_le _).trans hKL)
  have hmeet : RankOne.D R K ⊓ RankOne.D R L ≤ D := by
    rintro z ⟨hz₁,hz₂⟩
    refine ⟨hz₁.1,?_⟩
    have hc : K ⊔ L ≤ centralizer ({z} : Set G) := by
      apply sup_le
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (hz₁.2 k hk)
      · intro l hl
        exact mem_centralizer_singleton_iff.mpr (hz₂.2 l hl)
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hc ha)
  have hF₁F₂ : F₁ ≤ centralizer (F₂ : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (h.four_module_geometry hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc).2.2.2
  have hDF₁ : D ≤ centralizer (F₁ : Set G) := hD₁.trans hd₁.2.1
  have hDF₂ : D ≤ centralizer (F₂ : Set G) := hD₂.trans hd₂.2.1
  have hover : F₁ ⊓ (F₂ ⊔ D) ≤ D := by
    rintro z ⟨hz₁,hzo⟩
    have hzU : z ∈ U K := hd₁.2.2.2.2 ⟨hz₁,
      (sup_le (le_centralizer_iff.mp hF₁F₂) hDF₁) hzo⟩
    have hzD₂ : z ∈ RankOne.D R L := hU₁D₂ hzU
    have hm : z ∈ (F₂ : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left F₂ D
        (hDF₂.trans (Subgroup.centralizer_le_normalizer _))]
      exact hzo
    obtain ⟨a,ha,d,hd,rfl⟩ := hm
    have haD₂ : a ∈ RankOne.D R L := by simpa using (RankOne.D R L).mul_mem hzD₂ ((RankOne.D R L).inv_mem (hD₂ hd))
    have haU : a ∈ U L := (hd₂.2.2.2.1.le ⟨ha,haD₂⟩).1
    exact D.mul_mem (hmeet ⟨hU₂D₁ haU,haD₂⟩) hd
  have hF₁S : F₁ ≤ S R := sup_le h.module_le (h.conjugate_le hxR)
  have hF₂S : F₂ ≤ S R := sup_le h'.module_le (h'.conjugate_le hxR)
  have hspan : S R = (F₁ ⊔ F₂) ⊔ D := by
    change ChapterB.baumann R = _
    rw [hp.2.2.1,hp.1,Subgroup.map_sup]
    dsimp only [F₁,F₂,factor,D,S]
    ac_rfl
  have himD : baumannImage R f D = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨a,ha,rfl⟩
    exact MonoidHom.mem_ker.mp (hk ▸ ha)
  refine ⟨?_,?_,image_commuting f _ _ hF₁F₂⟩
  · have hs : baumannImage R f (S R) = ⊤ := by
      rw [baumannImage,subgroupOf_self,map_top_of_surjective f hf]
    rw [hspan,image_sup f _ _ (sup_le hF₁S hF₂S) inf_le_left,
      image_sup f _ _ hF₁S hF₂S,himD,sup_bot_eq] at hs
    exact hs
  · rw [disjoint_iff_inf_le]
    rintro z ⟨⟨a,ha,rfl⟩,b,hb,he⟩
    have hab : a / b ∈ f.ker := by
      change f (a / b) = 1
      rw [map_div,he,div_self']
    have habD : (a : G) / (b : G) ∈ D := by
      have hh : a / b ∈ D.subgroupOf (S R) := hk ▸ hab
      exact hh
    have haOther : (a : G) ∈ F₂ ⊔ D := by
      have hh := (F₂ ⊔ D).mul_mem (mem_sup_right habD) (mem_sup_left hb)
      change (a : G) / (b : G) * (b : G) ∈ F₂ ⊔ D at hh
      simpa only [div_mul_cancel] using hh
    have haD := hover ⟨ha,haOther⟩
    change f a = 1
    exact MonoidHom.mem_ker.mp (hk ▸ haD)

/-- The actual four choices in the quotient; no family or fixed profile is assumed. -/
theorem Setup.two_block_quotient_family
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M)
    (hxR : x ∈ normalizer (R : Set G)) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (f : S R →* T) (hf : Function.Surjective f)
    (hk : f.ker = (S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)).subgroupOf (S R)) :
    let u := baumannImage R f (U K)
    let v := baumannImage R f ((U K).map (MulAut.conj x⁻¹).toMonoidHom)
    let w := baumannImage R f (U L)
    let z := baumannImage R f ((U L).map (MulAut.conj x⁻¹).toMonoidHom)
    elementaryAbelianMaxSubgroups (⊤ : Subgroup T) = {u ⊔ w,u ⊔ z,v ⊔ w,v ⊔ z} := by
  let : Finite T := Finite.of_surjective f hf
  have hd := h.two_block_quotient_product h' hKL M T_H x hx hxR hindex hpair ht hnc f hf hk
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hk₁ : f.ker ≤ (RankOne.D R K).subgroupOf (S R) := by
    rw [hk]
    exact subgroupOf_mono _ (le_inf inf_le_left
      (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left))))
  have hk₂ : f.ker ≤ (RankOne.D R L).subgroupOf (S R) := by
    rw [hk]
    exact subgroupOf_mono _ (le_inf inf_le_left
      (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right))))
  have h1 := h.factor_image_family hxR hnc f hk₁
  have h2 := h'.factor_image_family hxR (second_noncommuting hi) f hk₂
  ext A
  rw [← hd.1,maxFamily_sup_iff_of_disjoint_of_commuting _ _ hd.2.1 hd.2.2]
  dsimp only [baumannImage]
  rw [h1,h2]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,exists_eq_or_imp,exists_eq_left,or_assoc]
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
