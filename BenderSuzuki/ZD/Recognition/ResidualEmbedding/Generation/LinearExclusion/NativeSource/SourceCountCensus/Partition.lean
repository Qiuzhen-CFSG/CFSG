module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Conjugates
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.SourceCountCensus.Torus

/-!
# Saturation of the source involution census

The disjoint TI family and A inject into the square-one elements, and the
torus family injects into their complement. Their source cardinalities add
to |R₁|. Both injections are consequently bijections, retaining literal
representatives for the inversion and fusion arguments.

Source: GLS4, Chapter 2, Lemma 15.6, counting paragraph.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
local notation "A" => closure (Z ∩ (M : Set G))
local notation "U" => twoCore M z t
local notation "R" => sourceNormalizer Z M z t
local notation "K" => residualCommutator M t

@[expose] public def squareParameters (Z : Set G) (M : Subgroup G) (z t : G) :=
  closure (Z ∩ (M : Set G)) ⊕
    (Σ C : conjugateFamily M z t, {x : C.val // x ≠ 1})

@[expose] public def squareMap (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    squareParameters Z M z t → {x : R // x ^ 2 = 1} :=
  Sum.elim
    (fun a => ⟨⟨a, (sup_le_sourceNormalizer d hs) ((show A ≤ A ⊔ U from le_sup_left) a.property)⟩,
      Subtype.ext (distinguished_square d a.property)⟩)
    (fun p => ⟨⟨p.2.val, conjugate_le_source d hs hg p.1 p.2.val.property⟩,
      Subtype.ext (conjugate_square d hs p.1 p.2.val.property)⟩)

public theorem squareMap_injective (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Function.Injective (squareMap d hs hg) := by
  intro a b he
  exact family_union_injective A R (fun C : conjugateFamily M z t => C.val)
    (le_sup_left.trans (sup_le_sourceNormalizer d hs)) (conjugate_le_source d hs hg)
    (conjugate_disjoint_distinguished d) (conjugate_pairwise_disjoint d)
    (by cases a <;> cases b <;> exact congrArg Subtype.val he)

public theorem squareParameters_card (hs : CentralizerLocalTwoData d) :
    Nat.card (squareParameters Z M z t) = (2 ^ n) ^ 2 * (Nat.card U - 1) + 2 ^ n := by
  classical
  let := Fintype.ofFinite (conjugateFamily M z t)
  rw [squareParameters, Nat.card_sum, Nat.card_sigma]
  simp only [card_nonidentity, conjugate_card, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card]
  have hcount : Nat.card (conjugateFamily M z t) = (2 ^ n) ^ 2 :=
    d.centralizer_twoCore_conjugates_card hs.twoCore_ne_bot
  rw [d.distinguished_elementary_card.2, hcount, add_comm]

@[expose] public def nonsquareMap (hs : CentralizerLocalTwoData d) (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (hx2 : x ^ 2 ≠ 1) : K × A → {y : R // y ^ 2 ≠ 1} :=
  fun p => ⟨⟨MulAut.conj (p.1 : G) x * p.2,
    (R).mul_mem (source_conj_mem d hg (torus_le_point d p.1.property) hx)
      ((sup_le_sourceNormalizer d hs) ((show A ≤ A ⊔ U from le_sup_left) p.2.property))⟩,
    fun he => torus_translate_nonsquare d hg hx hx2 p.1 p.2 (congrArg Subtype.val he)⟩

public theorem nonsquareMap_injective (hs : CentralizerLocalTwoData d) (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (hx2 : x ^ 2 ≠ 1) :
    Function.Injective (nonsquareMap d hs hg hx hx2) := by
  intro a b he
  exact torus_translate_injective d hs hg hx hx2
    (congrArg (fun y : {y : R // y ^ 2 ≠ 1} => (y.val : G)) he)

public theorem square_and_nonsquare_card (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Nat.card {x : R // x ^ 2 = 1} = (2 ^ n) ^ 2 * (Nat.card U - 1) + 2 ^ n ∧
    Nat.card {x : R // x ^ 2 ≠ 1} = 2 ^ n * (2 ^ n - 1) := by
  classical
  obtain ⟨x,hx,hx2⟩ := exists_nonsquare d hs hg
  have hl := Nat.card_le_card_of_injective _ (squareMap_injective d hs hg)
  rw [squareParameters_card d hs] at hl
  have hr := Nat.card_le_card_of_injective _ (nonsquareMap_injective d hs hg hx hx2)
  rw [Nat.card_prod, d.torus_structure.2.2.1, d.distinguished_elementary_card.2,
    mul_comm] at hr
  have hsum := Nat.card_congr (Equiv.sumCompl (fun y : R => y ^ 2 = 1))
  rw [Nat.card_sum] at hsum
  change Nat.card {y : R // y ^ 2 = 1} + Nat.card {y : R // y ^ 2 ≠ 1} = Nat.card R at hsum
  rw [hg.card] at hsum
  have hq : 0 < 2 ^ n := pow_pos (by decide) n
  have hu : 0 < Nat.card U := Nat.card_pos
  have hcalc : (2 ^ n) ^ 2 * (Nat.card U - 1) + 2 ^ n +
      2 ^ n * (2 ^ n - 1) = (2 ^ n) ^ 2 * Nat.card U := by
    have hr : Nat.card U - 1 + 1 = Nat.card U := Nat.sub_add_cancel hu
    have hq' : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel hq
    nlinarith
  omega

public theorem squareMap_bijective (hs : CentralizerLocalTwoData d) (hg : NormalizerData d) :
    Function.Bijective (squareMap d hs hg) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  exact ⟨squareMap_injective d hs hg,
    (squareParameters_card d hs).trans (square_and_nonsquare_card d hs hg).1.symm⟩

public theorem nonsquareMap_bijective (hs : CentralizerLocalTwoData d) (hg : NormalizerData d)
    {x : G} (hx : x ∈ R) (hx2 : x ^ 2 ≠ 1) :
    Function.Bijective (nonsquareMap d hs hg hx hx2) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨nonsquareMap_injective d hs hg hx hx2, ?_⟩
  rw [Nat.card_prod, d.torus_structure.2.2.1, d.distinguished_elementary_card.2,
    (square_and_nonsquare_card d hs hg).2, mul_comm]

end BenderSuzuki.ZD.LinearExclusion.SourceCount.Census
