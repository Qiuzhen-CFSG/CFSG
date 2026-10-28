module

public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterD.Section02.Defs
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer

/-!
# The full centralizer bound in D.2.21

The SQTK hypothesis belongs to the actual group covering `G`. Its odd
prime-rank bound is passed through that surjection, not imposed on the
quotient. Faithfulness of the elementary actor on `O₃(G)` makes every
nonidentity actor an involution acting nontrivially there. The local
section theorem then bounds the full `3`-rank of its centralizer.

Source: Aschbacher--Smith, D.2.21, printed p.188. The other D.2.17
conditions are not needed for this reduction.
-/

public section
namespace CFSG.Quasithin.ChapterD
open Subgroup Theory.GroupTheory

universe u v w
variable {H : Type u} [Group H] [Finite H] {G : Type v} [Group G] [Finite G]
  {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]

/-- D.2.21 on the literal SQTK covering group and its given surjection. -/
theorem source_lemma_D_2_21 {K : GroupClass.{u}} (hH : IsSQTK K H)
    (f : H →* G) (hf : Function.Surjective f)
    {ρ : Representation (ZMod 2) G V} {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hfaith : A ⊓ centralizer (pCore 3 G : Set G) = ⊥)
    {a : G} (ha : a ∈ A) (hne : a ≠ 1) :
    primeRank 3 (centralizer ({a} : Set G)) ≤ 1 := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a ha) hne
  have hmove : a ∉ centralizer (pCore 3 G : Set G) := by
    intro hc
    exact hne (mem_bot.mp (hfaith ▸ (show a ∈ A ⊓ centralizer (pCore 3 G : Set G) from ⟨ha, hc⟩)))
  exact primeRank_involutionCentralizer_le_one_of_surjective_rank_le_two
    (by decide : Odd 3) f hf (hH.stronglyQuasithin 3 (by decide) (by decide))
    (pCore 3 G) pCore_isPGroup a ha2 hmove

end CFSG.Quasithin.ChapterD
