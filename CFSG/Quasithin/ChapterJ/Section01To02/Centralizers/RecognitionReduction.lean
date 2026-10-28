module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.Defs
public import CFSG.Quasithin.ChapterI.Section06To08.StrongEmbedding
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# TI and strong embedding in the J.2.9 residual

Uniform centralizers of the nonidentity elements of the square-one subgroup
force TI by I.6.1: a conjugator of two such elements normalizes their common
centralizer, hence its square-one subgroup. If that common centralizer is
Sylow, the same calculation gives strong embedding of the proper normalizer.
The source application is to V inside L_s = O²(C_G(s)), with Sylow S₁.
The Sylow, square-one, uniform-centralizer and nonnormality premises still
have to be constructed from the earlier source deductions. SQTK recognition
and the Sz(8) isomorphism are not asserted here.

The order-seven group already lies in this literal residual; this uses
only its source order and centralization of s, not recognition.

Source: Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterJ.Centralizers
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_le_of_square_one_set (V P : Subgroup G)
    (hV : ∀ x : G, x ∈ V ↔ x ∈ P ∧ x ^ 2 = 1) :
    normalizer (P : Set G) ≤ normalizer (V : Set G) := by
  intro g hg x
  constructor
  · intro hx
    refine (hV _).mpr ⟨(hg x).mp ((hV x).mp hx).1, ?_⟩
    have h := congrArg (MulAut.conj g) ((hV x).mp hx).2
    simpa only [map_pow, map_one, MulAut.conj_apply] using h
  · intro hx
    refine (hV _).mpr ⟨(hg x).mpr ((hV _).mp hx).1, ?_⟩
    apply (MulAut.conj g).injective
    simpa only [map_pow, map_one, MulAut.conj_apply] using ((hV _).mp hx).2

/-- The I.6.1 step in J.2.9: the square-one subgroup is TI if all of its
nonidentity elements have the same centralizer. -/
theorem ti_of_uniform_centralizers (V P : Subgroup G)
    (hV : ∀ x : G, x ∈ V ↔ x ∈ P ∧ x ^ 2 = 1)
    (hC : ∀ x : G, x ∈ V → x ≠ 1 → centralizer ({x} : Set G) = P) :
    IsTISubgroup V := by
  have hN := normalizer_le_of_square_one_set V P hV
  apply lemma_I_6_1_1_of_mem_normalizer
  · intro x hx hne
    rw [hC x hx hne]
    exact le_normalizer.trans hN
  · intro x y hx hy hxy
    obtain ⟨g, hg⟩ := hxy
    by_cases hx1 : x = 1
    · exact ⟨1, by simpa [hx1] using hg⟩
    have hy1 : y ≠ 1 := by
      intro hy1
      apply hx1
      apply (MulAut.conj g).injective
      simpa only [map_one, MulAut.conj_apply] using hg.trans hy1
    have hm : P.map (MulAut.conj g).toMonoidHom ≤ P := by
      have h := map_centralizer_le_centralizer_image ({x} : Set G)
        (MulAut.conj g).toMonoidHom
      simpa only [Set.image_singleton, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, hg, hC x hx hx1, hC y hy hy1] using h
    have hn : g ∈ normalizer (P : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      apply eq_of_le_of_card_ge hm
      rw [card_map_of_injective (MulAut.conj g).injective]
    exact ⟨⟨g, hN hn⟩, hg⟩

/-- The strong-embedding step in J.2.9, with the Sylow and nonnormality
obligations explicit. No strong-embedding premise is assumed. -/
theorem stronglyEmbedded_of_uniform_centralizers (P : Sylow 2 G) (V : Subgroup G)
    (hV : ∀ x : G, x ∈ V ↔ x ∈ (P : Subgroup G) ∧ x ^ 2 = 1)
    (hC : ∀ x : G, x ∈ V → x ≠ 1 →
      centralizer ({x} : Set G) = (P : Subgroup G))
    (hproper : normalizer (V : Set G) ≠ ⊤) :
    BenderSuzuki.IsStronglyEmbedded (normalizer (V : Set G)) := by
  let M := normalizer (V : Set G)
  have hN := normalizer_le_of_square_one_set V (P : Subgroup G) hV
  have hPM : (P : Subgroup G) ≤ M := le_normalizer.trans hN
  have hVne : V ≠ ⊥ := by
    intro he
    apply hproper
    rw [he]
    exact normalizer_eq_top (H := (⊥ : Subgroup G))
  obtain ⟨⟨v, hv⟩, hv1⟩ := ne_bot_iff_exists_ne_one.mp hVne
  have hvm : v ∈ M := hPM ((hV v).mp hv).1
  have hvne : v ≠ 1 := fun he => hv1 (Subtype.ext he)
  have ho : orderOf (⟨v, hvm⟩ : M) = 2 := by
    apply orderOf_eq_prime _ (fun he => hvne (congrArg Subtype.val he))
    exact Subtype.ext ((hV v).mp hv).2
  have heven : Even (Nat.card M) := even_iff_two_dvd.mpr
    (ho ▸ orderOf_dvd_natCard (⟨v, hvm⟩ : M))
  have hmap : ((P.subtype hPM : Sylow 2 M) : Subgroup M).map M.subtype =
      (P : Subgroup G) := map_subgroupOf_eq_of_le hPM
  apply stronglyEmbedded_of_sylow_normalizer_and_centralizers M (P.subtype hPM)
    hproper heven
  · simpa only [hmap] using hN
  · intro i hi hiI
    rw [hmap] at hi
    rw [hC i ((hV i).mpr ⟨hi, hiI.sq_eq_one⟩) hiI.ne_one]
    exact hPM

namespace Choices
variable {d : LocalSetup G} (c : Choices d)

/-- The chosen seven-group centralizes the chosen s. -/
theorem B7_le_Gs : c.B7 ≤ c.Gs := by
  intro b hb
  exact mem_centralizer_singleton_iff.mpr (c.s_mem.2 b hb)

/-- The odd seven-group is contained in O²(C_G(s)), with the original embedding. -/
theorem B7_le_Ls : c.B7 ≤ c.Ls := by
  intro b hb
  refine mem_map.mpr ⟨⟨b, c.B7_le_Gs hb⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have hd : orderOf (⟨b, c.B7_le_Gs hb⟩ : c.Gs) ∣ 7 := by
    rw [← Subgroup.orderOf_coe (⟨b, c.B7_le_Gs hb⟩ : c.Gs), ← c.B7_card]
    exact c.B7.orderOf_dvd_natCard hb
  exact (by decide : Nat.Coprime 2 7).of_dvd_right hd

/-- Apply the proved criteria to the literal V, S₁ and L_s of J.2.9.
These are intermediate recognition hypotheses, not a recognition theorem. -/
theorem residual_ti_and_strongEmbedding
    (P : Sylow 2 c.Ls) (hP : (P : Subgroup c.Ls) = c.S1.subgroupOf c.Ls)
    (hV : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls ↔
      x ∈ c.S1.subgroupOf c.Ls ∧ x ^ 2 = 1)
    (hC : ∀ x : c.Ls, x ∈ d.V.subgroupOf c.Ls → x ≠ 1 →
      centralizer ({x} : Set c.Ls) = c.S1.subgroupOf c.Ls)
    (hproper : normalizer (d.V.subgroupOf c.Ls : Set c.Ls) ≠ ⊤) :
    IsTISubgroup (d.V.subgroupOf c.Ls) ∧
      BenderSuzuki.IsStronglyEmbedded (normalizer (d.V.subgroupOf c.Ls : Set c.Ls)) := by
  refine ⟨ti_of_uniform_centralizers _ _ hV hC, ?_⟩
  apply stronglyEmbedded_of_uniform_centralizers P _ _ _ hproper
  · simpa only [hP] using hV
  · simpa only [hP] using hC

end Choices
end CFSG.Quasithin.ChapterJ.Centralizers
