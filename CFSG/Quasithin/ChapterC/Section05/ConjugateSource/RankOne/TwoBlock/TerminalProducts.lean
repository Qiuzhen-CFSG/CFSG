module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SourceAveraging
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.MutualCentralizers
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.FixerNormalizer
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CentralCommutator

/-!
# The full centralizer product for the original two rank-one blocks

The two actual averaging conclusions intersect to control C_R(UUˣ).
The proved full-R mutual supplements then give C_R(U)=U C_R(K), with
K=K₁K₂ and U=U₁U₂. All intrinsic natural central covers remain intact.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
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

theorem Setup.two_block_full_centralizer_product
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : (∃ n, IsL2EvenBlock K n) →
      ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : (∃ n, IsL2EvenBlock L n) →
      ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    R ⊓ centralizer (U K ⊔ U L : Subgroup G) =
      (U K ⊔ U L) ⊔ (R ⊓ centralizer (K ⊔ L : Subgroup G)) := by
  let U₁ := U K
  let U₂ := U L
  let U₀ := U₁ ⊔ U₂
  let V₁ := U₁.conjBy x⁻¹
  let V₂ := U₂.conjBy x⁻¹
  let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
  let C₁ := R ⊓ centralizer (K : Set G)
  let C₂ := R ⊓ centralizer (L : Set G)
  let C := R ⊓ centralizer (K ⊔ L : Subgroup G)
  let P := R ⊓ centralizer (U₀ : Set G)
  let P' := R ⊓ centralizer (V : Set G)
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  obtain ⟨hp',ht'⟩ := reverse_block_pair hpair ht
  have hn1 := h.two_block_fixer_normalizes hKL h'.module_le M T_H hRTH x hx hxR hindex hpair ht hnc
  have hn2 := h'.two_block_fixer_normalizes (le_centralizer_iff.mp hKL) h.module_le M T_H hRTH
    x hx hxR hindex hp' ht' (second_noncommuting hi)
  have ha1 := h.source_common_centralizer_le hSylow hxR hnc hn1
  have ha2 := h'.source_common_centralizer_le hSylow' hxR (second_noncommuting hi) hn2
  have hU₁C₂ : U₁ ≤ C₂ := le_inf (h.module_le.trans inf_le_left)
    ((map_subtype_le _).trans (le_centralizer_iff.mp hKL))
  have hU₂C₁ : U₂ ≤ C₁ := le_inf (h'.module_le.trans inf_le_left)
    ((map_subtype_le _).trans hKL)
  have hC₁U₁ : C₁ ≤ centralizer (U₁ : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hC₂U₂ : C₂ ≤ centralizer (U₂ : Set G) := inf_le_right.trans (centralizer_le (map_subtype_le _))
  have hCC : C₁ ⊓ C₂ = C := by
    dsimp [C₁,C₂,C]
    rw [centralizer_join]
    ext a
    exact ⟨fun ha => ⟨ha.1.1,ha.1.2,ha.2.2⟩,fun ha => ⟨⟨ha.1,ha.2.1⟩,⟨ha.1,ha.2.2⟩⟩⟩
  have hV₁V : V₁ ≤ V := map_mono (show U₁ ≤ U₀ from le_sup_left)
  have hV₂V : V₂ ≤ V := map_mono (show U₂ ≤ U₀ from le_sup_right)
  have hcommon : P ⊓ P' ≤ U₀ ⊔ C := by
    have hh : P ⊓ P' ≤ (U₁ ⊔ C₁) ⊓ (U₂ ⊔ C₂) := by
      rintro c ⟨hc,hc'⟩
      exact ⟨ha1 ⟨⟨hc.1,centralizer_le (show U₁ ≤ U₀ from le_sup_left) hc.2⟩,centralizer_le hV₁V hc'.2⟩,
        ha2 ⟨⟨hc.1,centralizer_le (show U₂ ≤ U₀ from le_sup_right) hc.2⟩,centralizer_le hV₂V hc'.2⟩⟩
    rwa [product_intersection U₁ U₂ C₁ C₂
      (hC₁U₁.trans (Subgroup.centralizer_le_normalizer _))
      (hC₂U₂.trans (Subgroup.centralizer_le_normalizer _)) hU₁C₂ hU₂C₁,hCC] at hh
  let := h.elementary
  let := h'.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.sup_of_le_centralizer
    (hU₂C₁.trans hC₁U₁)
  have hUR : U₀ ≤ R := sup_le (h.module_le.trans inf_le_left) (h'.module_le.trans inf_le_left)
  have hUP : U₀ ≤ P := le_inf hUR (le_centralizer U₀)
  have hP'U : P' ≤ normalizer (U₀ : Set G) := by
    intro r hr
    have hh : r ∈ M ⊓ normalizer (FourModuleOrbit.modules U₁ U₂ x 2 : Set G) :=
      ⟨hTHM (hRTH hr.1),Subgroup.centralizer_le_normalizer _ (centralizer_le hV₁V hr.2)⟩
    have hnU₁ : r ∈ normalizer (U₁ : Set G) := ((hi.normalizers_eq 2 0) ▸ hh).2
    have hnU₂ : r ∈ normalizer (U₂ : Set G) := ((hi.normalizers_eq 2 1) ▸ hh).2
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp hnU₁,mem_normalizer_iff_map_conj_eq.mp hnU₂]
  have hmut := h.two_block_mutual_centralizers h' hR hKL hSylow hSylow' M T_H hRTH hTHM
    x hx hxR hindex hpair ht hnc
  change P = U₀ ⊔ C
  apply le_antisymm
  · intro p hp
    have hm : p ∈ (U₀ : Set G) * (P' : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U₀ P' hP'U]
      exact hmut.2 hp
    obtain ⟨u,hu,a,ha,rfl⟩ := hm
    have haP : a ∈ P := by
      have hh := P.mul_mem (P.inv_mem (hUP hu)) hp
      simpa only [inv_mul_cancel_left] using hh
    exact (U₀ ⊔ C).mul_mem (mem_sup_left hu) (hcommon ⟨haP,ha⟩)
  · refine sup_le hUP (le_inf inf_le_left ?_)
    exact inf_le_right.trans (centralizer_le (sup_le_sup (map_subtype_le _) (map_subtype_le _)))
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
