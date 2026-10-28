module

public import CFSG.Quasithin.ChapterA.Section04.Signalizers.NormalizerAction
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.InitialSource.XiMinus.FrattiniPair

/-!
# Transporting the original Xi automizer through the core normalizer

Every element of N_G(X) has the same action on X/O₂(X) as an element of
N_G(X) ∩ N_G(O₂(XT)). The section centralizer acts trivially on this exact
quotient, so the signalizer/Frattini factorization supplies the representative.
Only Xi membership and the original ambient Sylow subgroup are used.

As a literal consumer, two generating order-five Frattini factors preserved by
the core normalizer are preserved by the full normalizer. The construction of
those factors remains with the small-support argument; neither their existence
nor normalization of T or XT is asserted here.
Source: Aschbacher--Smith, Lemma 3.2.13, printed pp.584--585.
-/

public section
open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem sectionCentralizer_le_xiAction_ker (X : Subgroup G) :
    (twoSectionCentralizer X (normalizer (X : Set G))).subgroupOf
      (normalizer (X : Set G)) ≤ (Chapter3.xiQuotientNormalizerAction X).ker := by
  intro c hc
  apply MulEquiv.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) q
  change quotientAut (pCore 2 X) (X.normalizerMonoidHom c)
    (QuotientGroup.mk' (pCore 2 X) x) = QuotientGroup.mk' (pCore 2 X) x
  rw [quotientAut_apply_mk]
  have hm : ⁅(c : G), (x : G)⁆ ∈ X.pCoreIn 2 := hc.2.2 x x.property
  have hk : (X.normalizerMonoidHom c x) * x⁻¹ ∈ pCore 2 X := by
    obtain ⟨a, ha, he⟩ := mem_map.mp hm
    have hh : a = (X.normalizerMonoidHom c x) * x⁻¹ := Subtype.ext he
    exact hh ▸ ha
  have hq := (QuotientGroup.eq_one_iff _).mpr hk
  change QuotientGroup.mk' (pCore 2 X) ((X.normalizerMonoidHom c x) * x⁻¹) = 1 at hq
  rw [map_mul, map_inv] at hq
  exact mul_inv_eq_one.mp hq

/-- Preserve the literal X/O₂(X) action while moving into the core normalizer. -/
theorem source_normalizer_core_same_action (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G (T : Subgroup G)) (n : normalizer (X : Set G)) :
    ∃ m : ↥(normalizer (X : Set G) ⊓
        normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)),
      Chapter3.xiQuotientNormalizerAction X ⟨m, m.property.1⟩ =
        Chapter3.xiQuotientNormalizerAction X n :=
  normalizer_core_covers_action T X hX.perfect hX.invariant _
    (sectionCentralizer_le_xiAction_ker X) n

/-- The actual two-factor conclusion passes from the core normalizer to N_G(X). -/
theorem source_frattini_pair_of_core_normalizer (T : Sylow 2 G) {X : Subgroup G}
    (hX : X ∈ Chapter1.Xi G (T : Subgroup G))
    (B C : Subgroup (Chapter1.XiFrattiniQuotient X))
    (hB : Nat.card B = 5) (hC : Nat.card C = 5) (hne : B ≠ C) (hgen : B ⊔ C = ⊤)
    (hperm : ∀ m : ↥(normalizer (X : Set G) ⊓
        normalizer ((X ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)),
      let f := quotientAut (frattini (Chapter1.XiQuotient X))
        (Chapter3.xiQuotientNormalizerAction X ⟨m, m.property.1⟩)
      (B.map f.toMonoidHom = B ∧ C.map f.toMonoidHom = C) ∨
        (B.map f.toMonoidHom = C ∧ C.map f.toMonoidHom = B)) :
    HasNormalizerFrattiniPair X := by
  refine ⟨B, C, hB, hC, hne, hgen, ?_⟩
  intro n
  obtain ⟨m, hm⟩ := source_normalizer_core_same_action T hX n
  simpa only [hm] using hperm m

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource.InitialSource.XiMinus
