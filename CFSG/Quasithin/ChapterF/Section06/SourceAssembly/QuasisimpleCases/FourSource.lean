module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.FourCyclic
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# The complete group model and congruence in F.6.18(4)

The original common four-group normalizes the cubic local residual. Its
actual images in the prime-field PSL₂ model force the source congruence
p = ±11 modulo 24. This joins the established component sieve and cover
calculation to the local normalizer calculation, with the same field and
original subgroup maps. The cyclic-three-core consumer constructs the
quasisimple branch rather than assuming it.

Source: Aschbacher–Smith F.6.18(4), printed p.310.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {G₁ G₂ : Subgroup G}

theorem quasisimple_four_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], ChapterA.Section02.TheoremC κ S)
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4)
    (hL : pResidual 2 G = generalizedFitting G ∧ IsQuasisimple (pResidual 2 G)) :
    generalizedFitting G = ⊤ ∧ IsQuasisimple G ∧
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        Nonempty (G ≃* PSL(2, ZMod p)) := by
  have hcore : pCore 2 G = ⊥ := le_bot_iff.mp
    (twoCore_le_primeToThreeCore.trans (Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)
  obtain ⟨hF, hQ, p, hp, ho, _, h8, ⟨j⟩⟩ :=
    quasisimple_four_prime_model hA hC hH e h hT hL
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian 2 (G₁ ⊓ G₂ : Subgroup G) :=
    (four_intersection_models h hcore hT).1
  let V := (G₁ ⊓ G₂).map j.toMonoidHom
  let A := ((pResidual 2 G₁).map G₁.subtype).map j.toMonoidHom
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map j.toMonoidHom
  have hV : Nat.card V = 4 := (card_map_of_injective j.injective).trans hT
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hV]; decide)
  let : IsKleinFour V := ⟨hV, IsElementaryAbelian.exponent_eq_prime⟩
  have hAc : Nat.card A = 3 := by
    rw [card_map_of_injective j.injective, card_map_of_injective G₁.subtype_injective]
    exact h.local_residual_order_three (not_characteristic_two_of_intersection_four h hT)
  have hn : V ≤ normalizer (A : Set PSL(2, ZMod p)) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono h.intersection_normalizes_left_residual
  exact ⟨hF, hQ, p, hp, Theory.PSL2.prime_mod24_of_four_normalizes_cubic ho h8 V A hAc hn, ⟨j⟩⟩

theorem cyclic_four_models
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (S : Type u) [Group S] [Finite S], ChapterA.Section02.TheoremC κ S)
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (h : IsGoldschmidtTriple G₁ G₂) (hc : IsCyclic (pCore 3 G))
    (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 4) :
    generalizedFitting G = ⊤ ∧ IsQuasisimple G ∧
      ∃ p : ℕ, p.Prime ∧ (p % 24 = 11 ∨ p % 24 = 13) ∧
        Nonempty (G ≃* PSL(2, ZMod p)) :=
  quasisimple_four_models hA hC hH e h hT (cyclic_four_quasisimple_source hA hH e h hc hT)

end CFSG.Quasithin.ChapterF.SourceAssembly
