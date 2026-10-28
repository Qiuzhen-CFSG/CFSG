module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.Factors
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingQuotient.Enumeration
public import Stellmacher.ElementaryAbelianMaxProduct
/-!
# Maximum elementary subgroups in a conjugate factor

The actual centralizer-kernel projection S → UᵢUᵢˣ descends the marked
A₅ action. Its four-family lifts back through the literal factor embedding.
The inner Sylow exchange moves both extra members, leaving precisely Uᵢ
and Uᵢˣ invariant under R∩Kᵢ. No Frattini-triviality hypothesis is needed.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open RankOne AlternatingQuotient
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

theorem AlternatingPairSetup.conjugate_factor_family
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let F := U ⊔ V
    ∃ B₀ B₁ : Subgroup G,
      elementaryAbelianMaxSubgroups F = {U,V,B₀,B₁} ∧
      actionImage h.action B₀ = line 0 ∧ actionImage h.action B₁ = line 1 := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let F := U K ⊔ V
  have hd := h.conjugate_factor_product x hx hnc
  have hFS : F ≤ S R := le_sup_left.trans_eq hd.1.symm
  obtain ⟨f, hf, hker, hfix⟩ : ∃ f : S R →* F,
      Function.Surjective f ∧ f.ker = (D R K).subgroupOf (S R) ∧
      ∀ s : S R, (s : G) ∈ F → (f s : G) = (s : G) :=
    h.exists_conjugate_factor_projection x hx hnc
  have hk : f.ker ≤ (D R K).subgroupOf (S R) := hker.le
  have hPhi : (Phi R K).subgroupOf (S R) ≤ f.ker := by
    rw [hker]
    exact subgroupOf_mono _ (map_subtype_le _)
  have hi (A : Subgroup G) (hA : A ≤ F) : (baumannImage R f A).map F.subtype = A := by
    ext a
    constructor
    · rintro ⟨b, ⟨s, hs, rfl⟩, rfl⟩
      change (f s : G) ∈ A
      rw [hfix s (hA hs)]
      exact hs
    · intro ha
      refine ⟨f ⟨a, hFS (hA ha)⟩, ?_, ?_⟩
      · exact ⟨⟨a, hFS (hA ha)⟩, ha, rfl⟩
      · exact hfix _ (hA ha)
  have hiD : baumannImage R f (D R K) = ⊥ := by
    rw [baumannImage, Subgroup.map_eq_bot_iff]
    exact hker.ge
  have hiQ : (baumannImage R f (Q R K)).map F.subtype = U K := by
    have hp : Q R K = U K ⊔ D R K := h.product
    rw [hp, image_sup f (U K) (D R K) h.module_le inf_le_left, hiD, sup_bot_eq]
    exact hi _ le_sup_left
  have hiV : (baumannImage R f ((Q R K).map (MulAut.conj x⁻¹).toMonoidHom)).map F.subtype = V := by
    rw [← h.opposite_eq_conjugate x hx hnc,
      image_sup f _ _ (le_sup_right.trans hFS) inf_le_left, hiD, sup_bot_eq]
    exact hi _ le_sup_right
  obtain ⟨B₀, B₁, hfamily, h0, h1⟩ := quotient_family_eq_four h x hx hnc f hf hPhi hk
  have himage (B : Subgroup F) : baumannImage R f (B.map F.subtype) = B :=
    (map_injective F.subtype_injective) (hi _ (map_subtype_le B))
  refine ⟨B₀.map F.subtype, B₁.map F.subtype, ?_, ?_, ?_⟩
  · change elementaryAbelianMaxSubgroups F = {U K, V, B₀.map F.subtype, B₁.map F.subtype}
    ext A
    rw [maxFamily_equiv_iff F (MulEquiv.refl F) A]
    simp only [hfamily, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨B, hB, he⟩
      change A = B.map F.subtype at he
      rcases hB with rfl | rfl | rfl | rfl
      · exact Or.inl (he.trans hiQ)
      · exact Or.inr (Or.inl (he.trans hiV))
      · exact Or.inr (Or.inr (Or.inl he))
      · exact Or.inr (Or.inr (Or.inr he))
    · rintro (he | he | he | he)
      · exact ⟨_, Or.inl rfl, he.trans hiQ.symm⟩
      · exact ⟨_, Or.inr (Or.inl rfl), he.trans hiV.symm⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), he⟩
      · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), he⟩
  · have ha := image_action h f hf hk (B₀.map F.subtype) ((map_subtype_le _).trans hFS)
    rw [himage B₀, h0] at ha
    exact ha.symm
  · have ha := image_action h f hf hk (B₁.map F.subtype) ((map_subtype_le _).trans hFS)
    rw [himage B₁, h1] at ha
    exact ha.symm

theorem AlternatingPairSetup.conjugate_factor_invariant_family
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let F := U ⊔ V
    {A ∈ elementaryAbelianMaxSubgroups F | R ⊓ K ≤ normalizer (A : Set G)} = {U,V} := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let F := U K ⊔ V
  obtain ⟨B₀,B₁,hfamily,h0,h1⟩ := h.conjugate_factor_family x hx hnc
  change elementaryAbelianMaxSubgroups F = {U K,V,B₀,B₁} at hfamily
  have hFS : F ≤ S R := le_sup_left.trans_eq (h.conjugate_factor_product x hx hnc).1.symm
  obtain ⟨r,hr,he⟩ := h.pairExchange_mem
  have h0F : B₀ ≤ F := (show B₀ ∈ elementaryAbelianMaxSubgroups F by rw [hfamily]; simp).1
  have h1F : B₁ ≤ F := (show B₁ ∈ elementaryAbelianMaxSubgroups F by rw [hfamily]; simp).1
  have hm0 := moved_of_line_zero h.action ((h0F.trans hFS).trans le_sup_right) h0 r he
  have hm1 := moved_of_line_one h.action ((h1F.trans hFS).trans le_sup_right) h1 r he
  have hn := h.transvection_normalizes x hx
  change {A ∈ elementaryAbelianMaxSubgroups F | R ⊓ K ≤ normalizer (A : Set G)} = {U K,V}
  ext A
  constructor
  · rintro ⟨hA,hNA⟩
    rw [hfamily] at hA
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hA ⊢
    rcases hA with heq | heq | heq | heq
    · exact Or.inl heq
    · exact Or.inr heq
    · subst A
      exact (hm0 (mem_normalizer_iff_map_conj_eq.mp (hNA hr)).symm).elim
    · subst A
      exact (hm1 (mem_normalizer_iff_map_conj_eq.mp (hNA hr)).symm).elim
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨by rw [hfamily]; simp, hn.2.2.trans hn.1⟩
    · have ha := Set.mem_singleton_iff.mp ha
      subst A
      exact ⟨by rw [hfamily]; simp, hn.2.2.trans hn.2.1⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
