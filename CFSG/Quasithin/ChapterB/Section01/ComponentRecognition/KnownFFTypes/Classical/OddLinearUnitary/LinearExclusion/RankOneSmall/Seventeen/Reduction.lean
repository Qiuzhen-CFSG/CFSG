module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Reduction
public import Theory.Representation.BinaryTwoPowerDegree
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.SpecificGroups.PSL2.SeventeenFrobenius

/-!
# The degree-eight PSL₂(17) exclusion: assembly of the local calculations

The source hypotheses and the explicit degree bound force binary degree
exactly eight. Nilpotent kernel stabilization rules out order sixteen even
in the conjugation image, which is the obstruction to a diagonal extension.

For the final actor argument, the fourth power of a Frobenius complement
generator has displacement four, and its square has displacement six.
Involution fusion and the involution-centralizer product put these operators
in the original actor group. Saturation forces every small actor to have
rank two and a common fixed space; the product then contradicts that equality.

The theorem `source_exclusion_of_local_calculations` is conditional: the
Frobenius-module calculation and the actual-group fusion/product construction
are still explicit premises. This is not yet the completed PSL₂(17) exclusion.
Their discharge and the unconditional theorem remain with this module's owner.

Source: Aschbacher--Smith K.2, printed p.453; Guralnick--Malle,
*Classification of 2F-modules I*, Proposition 4.1, manuscript p.9.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : SourceAction ρ)

/-- The constructed matrix Frobenius subgroup forces degree eight in every
faithful binary action of the actual PSL₂(17) model. The next local calculation
must determine the complement's fixed spaces in the equality case. -/
theorem model_frobenius_degree_lower_bound
    (τ : Representation (ZMod 2) Theory.PSL2.SeventeenFrobenius.Model V)
    (hf : Function.Injective τ) : 8 ≤ Module.finrank (ZMod 2) V := by
  let : Nontrivial Theory.PSL2.SeventeenFrobenius.kernel :=
    (Finite.one_lt_card_iff_nontrivial (α := Theory.PSL2.SeventeenFrobenius.kernel)).mp
      (by rw [Theory.PSL2.SeventeenFrobenius.kernel_card]; decide)
  have horder : (Nat.card Theory.PSL2.SeventeenFrobenius.kernel : ZMod 2) ≠ 0 := by
    rw [Theory.PSL2.SeventeenFrobenius.kernel_card]
    decide
  simpa only [Theory.PSL2.SeventeenFrobenius.complement_card] using
    card_le_finrank_of_fixedPointFree_normalizer_of_field τ
      Theory.PSL2.SeventeenFrobenius.kernel Theory.PSL2.SeventeenFrobenius.complement
      hf horder Theory.PSL2.SeventeenFrobenius.complement_normalizes
      Theory.PSL2.SeventeenFrobenius.complement_free

include h

/-- The explicit upper bound in this task makes the degree exactly eight. -/
theorem source_degree_eq_eight
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (hd : Module.finrank (ZMod 2) V ≤ 8) : Module.finrank (ZMod 2) V = 8 :=
  Nat.le_antisymm hd (eight_le_degree_seventeen ρ h.faithful hm)

/-- The original group and each of its action images exclude order sixteen.
In particular this applies to conjugation on the literal central quotient. -/
theorem source_image_order_ne_sixteen (hd : Module.finrank (ZMod 2) V ≤ 8)
    {H : Type*} [Monoid H] (f : G →* H) (g : G) : orderOf (f g) ≠ 16 :=
  BinaryTwoPowerDegree.image_order_ne_sixteen ρ h.faithful hd f g

omit [FiniteDimensional (ZMod 2) V] in
private theorem odd_card_of_le_source_centralizer (S : Subgroup G)
    (hS : S ≤ centralizer (generalizedFitting G : Set G)) : Odd (Nat.card S) := by
  let : IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  by_contra hn
  have hd : 2 ∣ Nat.card S := by
    simpa only [Nat.not_odd_iff_even, even_iff_two_dvd] using hn
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hd
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have he : (t : G) = 1 := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
    ρ (generalizedFitting G) h.faithful (congrArg S.subtype ht2) (hS t.property)
  have ht1 : t = 1 := Subtype.ext he
  simp only [ht1, orderOf_one] at ht
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Schur's argument excludes involutions in the full ambient centralizer. -/
theorem source_centralizer_odd_card :
    Odd (Nat.card (centralizer (generalizedFitting G : Set G))) :=
  odd_card_of_le_source_centralizer ρ h _ le_rfl

omit [FiniteDimensional (ZMod 2) V] in
/-- The compatible cover has odd center; it is not assumed to be centerless. -/
theorem source_center_odd_card : Odd (Nat.card (center (generalizedFitting G))) := by
  have hc : (center (generalizedFitting G)).map (generalizedFitting G).subtype ≤
      centralizer (generalizedFitting G : Set G) := by
    rintro z ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    exact congrArg (generalizedFitting G).subtype ((mem_center_iff.mp hy) ⟨l, hl⟩)
  have ho := odd_card_of_le_source_centralizer ρ h _ hc
  rwa [Subgroup.card_map_of_injective Subtype.val_injective] at ho

omit h [Finite G] in
private theorem conjugate_fixedCodim {a b : G} (hc : IsConj a b) :
    fixedCodim ρ (zpowers b) = fixedCodim ρ (zpowers a) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  exact fixedCodim_zpowers_conj ρ a g

/-- Displacement four for involutions and six for the centralizer product
exclude every elementary actor at threshold two, including rank-one actors.
The local premises concern the same elements and representation in G. -/
theorem source_exclusion_of_local_calculations
    (hm : ClassicalGroup.IsPSL
      ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 17)
    (r : G)
    (hfour : fixedCodim ρ (zpowers (r ^ 4)) = 4)
    (htwo : fixedCodim ρ (zpowers (r ^ 2)) = 6)
    (hfusion : ∀ t : G, orderOf t = 2 → IsConj (r ^ 4) t)
    (hproducts : ∀ A : Subgroup G, IsElementaryTwo A → rank A = 2 →
      ∃ t g a b : G, t ∈ A ∧ orderOf t = 2 ∧ Commute g t ∧ a ∈ A ∧ b ∈ A ∧
        IsConj (r ^ 2) (a * (g * b * g⁻¹))) :
    2 < cubicRatio ρ := by
  by_contra hn
  obtain ⟨A, hA, _, hsmall⟩ := (cubicRatio_le_nat_iff ρ 2).mp (le_of_not_gt hn)
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : orderOf t = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian t ht) ht1
  have htlarge : 4 ≤ fixedCodim ρ (zpowers t) := by
    rw [conjugate_fixedCodim ρ (hfusion t ht2), hfour]
  obtain ⟨hr, _, _⟩ := source_prime_actor_saturation ρ h
    (by decide : Nat.Prime 17) (by decide) (by decide) hm hA hsmall ht htlarge
  obtain ⟨s, g, a, b, hs, hs2, hg, ha, hb, hp⟩ := hproducts A hA hr
  apply source_prime_not_small_actor_of_product ρ h
    (by decide : Nat.Prime 17) (by decide) (by decide) hm hA hs
      (by rw [conjugate_fixedCodim ρ (hfusion s hs2), hfour]) hg ha hb ?_ hsmall
  rw [conjugate_fixedCodim ρ hp, htwo]
  decide

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
