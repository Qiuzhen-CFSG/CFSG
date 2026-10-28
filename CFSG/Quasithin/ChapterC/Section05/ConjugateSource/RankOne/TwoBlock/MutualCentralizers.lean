module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceCentralizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.NormalizerOrbit

/-!
# Mutual full-R centralizers of the two original rank-one modules

The intrinsic model calculation applies to both source blocks. Their four-module
orbit supplies the second noncommutation and all needed normalizer inclusions.
Intersecting the individual supplements gives the total supplement. Conjugation
by the original x gives its symmetric partner, since x² fixes every module.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G]
private theorem centralizer_join (A B : Subgroup G) :
    centralizer (A ⊔ B : Subgroup G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

private theorem product_intersection (A B D E : Subgroup G)
    (hDA : D ≤ normalizer (A : Set G)) (hEB : E ≤ normalizer (B : Set G))
    (hAE : A ≤ E) (hBD : B ≤ D) :
    (A ⊔ D) ⊓ (B ⊔ E) = (A ⊔ B) ⊔ (D ⊓ E) := by
  apply le_antisymm
  · rintro g ⟨hg1, hg2⟩
    have hgm : g ∈ (A : Set G) * (D : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A D hDA]
      exact hg1
    obtain ⟨a, ha, d, hd, rfl⟩ := hgm
    have hdBE : d ∈ B ⊔ E := by
      simpa using (B ⊔ E).mul_mem ((B ⊔ E).inv_mem ((show E ≤ B ⊔ E from le_sup_right) (hAE ha))) hg2
    have hdm : d ∈ (B : Set G) * (E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left B E hEB]
      exact hdBE
    obtain ⟨b, hb, e, he, rfl⟩ := hdm
    have heD : e ∈ D := by simpa using D.mul_mem (D.inv_mem (hBD hb)) hd
    have hh := mul_mem_sup (mul_mem_sup ha hb) (show e ∈ D ⊓ E from ⟨heD, he⟩)
    simpa only [mul_assoc] using hh
  · apply sup_le
    · exact sup_le (le_inf le_sup_left (hAE.trans le_sup_right))
        (le_inf (hBD.trans le_sup_right) le_sup_left)
    · exact le_inf (inf_le_left.trans le_sup_right) (inf_le_right.trans le_sup_right)


private theorem map_centralizer (B : Subgroup G) (e : G ≃* G) :
    (centralizer (B : Set G)).map e.toMonoidHom = centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e y) (mem_map_of_mem _ hy)

private theorem reverse_block_pair {M T K L : Subgroup G}
    (hp : ∀ g ∈ T, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T ∧ K.conjBy (t : G) = L) :
    (∀ g ∈ T, L.conjBy g = L ∨ L.conjBy g = K) ∧
      ∃ t : M, (t : G) ∈ T ∧ L.conjBy (t : G) = K := by
  obtain ⟨t,ht,he⟩ := ht
  constructor
  · intro g hg
    have hh := hp (g*(t:G)) (T.mul_mem hg ht)
    rw [Subgroup.conjBy_mul,he] at hh
    exact hh.symm
  · refine ⟨t⁻¹,T.inv_mem ht,?_⟩
    rw [← he]
    exact Subgroup.conjBy_inv _ _

variable [Finite G] {R K L : Subgroup G} {F F' : Type*} [Field F] [Field F']

/-- This is the actual source supplement for the total U, with both genuine
Sylow inputs isolated at their earlier C.5.4 boundary. -/
theorem Setup.two_block_mutual_centralizers
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : (∃ n, IsL2EvenBlock L n) →
      ∃ P : Sylow 2 L, (P : Subgroup L).map L.subtype = S R ⊓ L)
    (M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let U₀ := U K ⊔ U L
    let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
    R ⊓ centralizer (V : Set G) ≤ V ⊔ (R ⊓ centralizer (U₀ : Set G)) ∧
      R ⊓ centralizer (U₀ : Set G) ≤ U₀ ⊔ (R ⊓ centralizer (V : Set G)) := by
  let U₁ := U K
  let U₂ := U L
  let V₁ := U₁.conjBy x⁻¹
  let V₂ := U₂.conjBy x⁻¹
  let U₀ := U₁ ⊔ U₂
  let V := V₁ ⊔ V₂
  let C₁ := R ⊓ centralizer (U₁ : Set G)
  let C₂ := R ⊓ centralizer (U₂ : Set G)
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  obtain ⟨hp',ht'⟩ := reverse_block_pair hpair ht
  have hn1 := h.two_block_centralizer_normalizes hKL h'.module_le M T_H hRTH hTHM x hx hxR hindex hpair ht hnc
  have hn2 := h'.two_block_centralizer_normalizes (le_centralizer_iff.mp hKL) h.module_le
    M T_H hRTH hTHM x hx hxR hindex hp' ht' (second_noncommuting hi)
  have hf1 := h.source_full_centralizer_le hR hSylow hxR hnc hn1
  have hf2 := h'.source_full_centralizer_le hR hSylow' hxR (second_noncommuting hi) hn2
  have hn (i j : Fin 4) : R ⊓ centralizer (FourModuleOrbit.modules U₁ U₂ x i : Set G) ≤
      normalizer (FourModuleOrbit.modules U₁ U₂ x j : Set G) := by
    rintro r ⟨hr,hc⟩
    have hh : r ∈ M ⊓ normalizer (FourModuleOrbit.modules U₁ U₂ x i : Set G) :=
      ⟨hTHM (hRTH hr),Subgroup.centralizer_le_normalizer _ hc⟩
    rw [hi.normalizers_eq i j] at hh
    exact hh.2
  have hV1R : V₁ ≤ R := (h.conjugate_le hxR).trans inf_le_left
  have hV2R : V₂ ≤ R := (h'.conjugate_le hxR).trans inf_le_left
  have hcross := FourModuleOrbit.cross_commutators hi.toInputs
  have hV1C2 : V₁ ≤ C₂ := le_inf hV1R (commutator_eq_bot_iff_le_centralizer.mp hcross.2.2.1)
  have hV2C1 : V₂ ≤ C₁ := le_inf hV2R
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross.2.1))
  have hCC : C₁ ⊓ C₂ = R ⊓ centralizer (U₀ : Set G) := by
    rw [centralizer_join]
    change (R ⊓ centralizer (U₁ : Set G)) ⊓ (R ⊓ centralizer (U₂ : Set G)) = _
    ext a
    exact ⟨fun ha => ⟨ha.1.1,ha.1.2,ha.2.2⟩,fun ha => ⟨⟨ha.1,ha.2.1⟩,⟨ha.1,ha.2.2⟩⟩⟩
  have hf : R ⊓ centralizer (V : Set G) ≤ V ⊔ (R ⊓ centralizer (U₀ : Set G)) := by
    have hl : R ⊓ centralizer (V : Set G) ≤ (V₁ ⊔ C₁) ⊓ (V₂ ⊔ C₂) := by
      rintro a ⟨ha,hc⟩
      exact ⟨hf1 ⟨ha,centralizer_le (show V₁ ≤ V from le_sup_left) hc⟩,
        hf2 ⟨ha,centralizer_le (show V₂ ≤ V from le_sup_right) hc⟩⟩
    rwa [product_intersection V₁ V₂ C₁ C₂ (hn 0 2) (hn 1 3) hV1C2 hV2C1,hCC] at hl
  have hVmap : U₀.map (MulAut.conj x⁻¹).toMonoidHom = V := Subgroup.map_sup _ _ _
  have hUx2 : U₀.conjBy (x^2) = U₀ := by
    change (U₁ ⊔ U₂).map (MulAut.conj (x^2)).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) (FourModuleOrbit.x_square_fixes_modules hi.toInputs 0) (FourModuleOrbit.x_square_fixes_modules hi.toInputs 1)
  have hUx : U₀.conjBy x = V := by
    rw [← hVmap]
    change U₀.conjBy x = U₀.conjBy x⁻¹
    calc
      U₀.conjBy x = (U₀.conjBy (x^2)).conjBy x⁻¹ := by
        rw [← Subgroup.conjBy_mul]
        congr 1
        group
      _ = U₀.conjBy x⁻¹ := congrArg (fun W : Subgroup G => W.conjBy x⁻¹) hUx2
  have hVx : V.conjBy x = U₀ := by
    rw [← hVmap]
    exact Subgroup.conjBy_inv' _ _
  have hRx : R.map (MulAut.conj x).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hxR
  have hback := map_mono (f := (MulAut.conj x).toMonoidHom) hf
  have hC (W : Subgroup G) : (R ⊓ centralizer (W : Set G)).map (MulAut.conj x).toMonoidHom =
      R ⊓ centralizer (W.conjBy x : Set G) := by
    rw [map_inf _ _ _ (MulAut.conj x).injective,map_centralizer,hRx]
    rfl
  rw [Subgroup.map_sup V (R ⊓ centralizer (U₀ : Set G)),hC,hC] at hback
  change R ⊓ centralizer (V.conjBy x : Set G) ≤ V.conjBy x ⊔
    (R ⊓ centralizer (U₀.conjBy x : Set G)) at hback
  rw [hVx,hUx] at hback
  change R ⊓ centralizer (U₀.map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ _ ∧ _
  rw [hVmap]
  exact ⟨hf,hback⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
