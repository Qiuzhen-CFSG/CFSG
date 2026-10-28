module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.SectionNormalizer
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.QuasithinBasic
public import Theory.ElementaryAbelian.Injective

/-!
# A nontrivial kernel in an elementary local action

An elementary binary subgroup larger than the rank bound of a full induced
automizer contains a nonidentity centralizing element. Pulling the actor back
through an ambient equivalence gives the same conclusion on a literal mapped
factor. This is the rank-kernel step used in source 10.2.12.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

theorem exists_nontrivial_centralizer_of_local_rank
    (A W M : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ M ⊓ normalizer (W : Set G)) {r : ℕ}
    (hr : primeRank 2 (inducedAutomizer W M) ≤ r)
    (hcard : 2 ^ r < Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ centralizer (W : Set G) := by
  by_contra! h
  let f := (localNormalizerAction W M).comp (inclusion hA)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    apply Subtype.ext
    by_contra hne
    exact h a a.property hne
      ((localNormalizerAction_eq_one_iff W M (inclusion hA a)).mp ha)
  have hrA := (Theory.GroupTheory.primeRank_le_of_injective 2 f hf).trans hr
  have hc := (primeRank_le_iff_elementary_card_le A).mp hrA ⊤
    (IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype Subtype.val_injective)
  rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv] at hc
  exact (not_lt_of_ge hc) hcard

theorem exists_nontrivial_centralizer_of_local_rank_map
    (A W M : Subgroup G) [IsElementaryAbelian 2 A]
    (e : G ≃* G)
    (hA : A ≤ M.map e.toMonoidHom ⊓ normalizer (W.map e.toMonoidHom : Set G))
    {r : ℕ} (hr : primeRank 2 (inducedAutomizer W M) ≤ r)
    (hcard : 2 ^ r < Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ centralizer (W.map e.toMonoidHom : Set G) := by
  let B := A.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBM : B ≤ M := by
    simpa [B, map_map] using map_mono (f := e.symm.toMonoidHom) (hA.trans inf_le_left)
  have hBN : B ≤ normalizer (W : Set G) := by
    have hh := (map_mono (f := e.symm.toMonoidHom) (hA.trans inf_le_right)).trans
      ((W.map e.toMonoidHom).le_normalizer_map e.symm.toMonoidHom)
    simpa [B, map_map] using hh
  have hc : 2 ^ r < Nat.card B := by
    rw [show Nat.card B = Nat.card A from
      (Nat.card_congr (Subgroup.equivMapOfInjective A e.symm.toMonoidHom e.symm.injective).toEquiv).symm]
    exact hcard
  obtain ⟨b,hb,hbne,hbc⟩ := exists_nontrivial_centralizer_of_local_rank B W M
    (le_inf hBM hBN) hr hc
  refine ⟨e b,?_,?_,?_⟩
  · have hh := mem_map_of_mem e.toMonoidHom hb
    simpa [B, map_map] using hh
  · exact fun he => hbne (e.injective (he.trans (map_one e).symm))
  · rintro x ⟨w,hw,rfl⟩
    simpa only [←map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hbc w hw)

end CFSG.Quasithin.ChapterE
