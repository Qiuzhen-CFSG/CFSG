module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicFamily
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeCyclicMoving
/-!
# Globalization of the cyclic local alternative in D.2.26–29

When every minimum involution has a cubic three-core commutator, the
original SQTK cover makes [O₃,G] elementary of order three or nine. In
the latter case its four-space cubic factors form a family of at most
three members. The small-family and three-plane arguments both supply
a normal cubic factor. The original indecomposable action then makes
that factor fully moved and gives the required odd-kernel generation.

This assembles the literal original source hypotheses, without a module
model or normal-factor premise. Source: Aschbacher–Smith, printed
pp.191–192, D.2.26–29.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

theorem Hypotheses.all_local_cyclic_three_localGeneration (h : Hypotheses ρ)
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3) :
    Nonempty (LocalGeneration ρ) := by
  rcases h.toCoreHypotheses.threeCore_commutator_card_three_or_nine
    hH f honto hfive hcyc with h3 | h9
  · exact h.threeCore_commutator_cubic_localGeneration hq hfive hNo hcyc h3
  by_cases hs : Nat.card {D : Subgroup G | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4} ≤ 2
  · exact h.small_fourSpace_family_localGeneration hq hfive hNo hcyc hs
  let : IsElementaryAbelian 3 (⁅pCore 3 G,⊤⁆ : Subgroup G) :=
    (h.toCoreHypotheses.threeCore_structure_of_cyclic_commutators
      hH f honto hfive hcyc).2.2
  have hs3 : Nat.card {D : Subgroup G | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4} = 3 := by
    have hh := nine_support_card_le_three ρ ⁅pCore 3 G,⊤⁆ h9
      (h.threeCore_commutator_fixed_eq_bot hq hfive hNo)
    change Nat.card {D : Subgroup G | D ≤ ⁅pCore 3 G,⊤⁆ ∧ Nat.card D = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4} ≤ 3 at hh
    omega
  obtain ⟨D,hDE,hD,hW,hDn⟩ :=
    h.nine_three_factor_normal hH f honto hq hfive hNo hcyc h9 hs3
  let : D.Normal := hDn
  exact h.normal_cubic_localGeneration hq hfive hNo hcyc D
    (hDE.trans (commutator_le_left _ _)) hD hW
end CFSG.Quasithin.ChapterD.CyclicSource
