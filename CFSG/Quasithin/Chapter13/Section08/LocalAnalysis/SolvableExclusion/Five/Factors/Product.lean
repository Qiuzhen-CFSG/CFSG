module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.SupportGeneration
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# Actual products of the five-factors and their supports

The commuting independent factors give an isomorphism from their product
to the supplied P. The same construction identifies the product of their
actual supports with the full P-displacement. On each single coordinate
both isomorphisms are the original subgroup inclusions. In particular the
orders are 5^s and 16^s, respectively.

These consequences use the construction contract `Factorization`; they do
not assert its existence. The source factor construction must supply that
contract from D.2.17 and the minimal solvable local configuration.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951, the direct product and direct sum in the five-primary case.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
variable {G : Type*} [Group G]
variable {H UH V₁ : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable {a : StarAction H UH V₁} {P : Subgroup G}

private theorem Factorization.pairwise_commute (f : Factorization a P) :
    Pairwise fun i j => ∀ x y : G, x ∈ f.factor i → y ∈ f.factor j → Commute x y := by
  intro i j hij x y hx hy
  have hc := commutator_eq_bot_iff_le_centralizer.mp (f.commute i j hij) hx
  exact (mem_centralizer_iff.mp hc y hy).symm

/-- The internal product map uses the literal inclusions of the five-factors. -/
noncomputable def Factorization.productEquiv (f : Factorization a P) :
    (∀ i, f.factor i) ≃* P := by
  let q : (∀ i, f.factor i) →* G :=
    noncommPiCoprod (by exact Factorization.pairwise_commute f)
  have hi : Function.Injective q := injective_noncommPiCoprod_of_iSupIndep f.factor_independent
  have hr : q.range = P := noncommPiCoprod_range.trans f.generated.symm
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)

theorem Factorization.productEquiv_single (f : Factorization a P)
    (i : Fin f.count) (x : f.factor i) :
    (f.productEquiv (Pi.mulSingle i x) : G) = (x : G) := by
  change noncommPiCoprod (Factorization.pairwise_commute f) (Pi.mulSingle i x) = (x : G)
  exact noncommPiCoprod_mulSingle i x

theorem Factorization.card_eq (f : Factorization a P) : Nat.card P = 5 ^ f.count := by
  rw [← Nat.card_congr f.productEquiv.toEquiv, Nat.card_pi]
  simp only [f.factor_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The support product maps each point by its actual subgroup inclusion. -/
noncomputable def Factorization.supportProductEquiv [IsMulCommutative UH]
    (f : Factorization a P) (hPH : P ≤ H) :
    (∀ i, f.support i) ≃* commutatorAction (a.actors P) (UH ⧸ V₁.subgroupOf UH) := by
  have hc : Pairwise fun i j => ∀ x y : UH ⧸ V₁.subgroupOf UH,
      x ∈ f.support i → y ∈ f.support j → Commute x y := by
    intro i j _ x y _ _
    exact Commute.all x y
  let q := noncommPiCoprod hc
  have hi : Function.Injective q := injective_noncommPiCoprod_of_iSupIndep f.support_independent
  have hr : q.range = commutatorAction (a.actors P) (UH ⧸ V₁.subgroupOf UH) :=
    noncommPiCoprod_range.trans (f.support_generated hPH).symm
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)

theorem Factorization.supportProductEquiv_single [IsMulCommutative UH]
    (f : Factorization a P) (hPH : P ≤ H) (i : Fin f.count) (x : f.support i) :
    (f.supportProductEquiv hPH (Pi.mulSingle i x) : UH ⧸ V₁.subgroupOf UH) =
      (x : UH ⧸ V₁.subgroupOf UH) := by
  exact noncommPiCoprod_mulSingle
    (hcomm := fun _ _ _ x y _ _ => Commute.all x y) i x

theorem Factorization.full_support_card [IsMulCommutative UH]
    (f : Factorization a P) (hPH : P ≤ H) :
    Nat.card (commutatorAction (a.actors P) (UH ⧸ V₁.subgroupOf UH)) = 16 ^ f.count := by
  rw [← Nat.card_congr (f.supportProductEquiv hPH).toEquiv, Nat.card_pi]
  simp only [Factorization.support, f.support_card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
