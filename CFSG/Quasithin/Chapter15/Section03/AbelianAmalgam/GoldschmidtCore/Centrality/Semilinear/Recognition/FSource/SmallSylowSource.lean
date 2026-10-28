module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.NoncyclicSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.FourSource
public import Mathlib.Algebra.Field.ULift
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence
/-!
# Complete source F.6.18 for a common Sylow subgroup of order at most four

The noncyclic three-core branch is already classified by F.6.16. In the
cyclic case a genuine component excludes an order-two Sylow subgroup;
order four forces the quasisimple residual to be the whole group. The
actual Theorem C sieve and central-cover descent give PSL₂(p). The original
four-group normalizes the cubic local residual, forcing p = ±11 modulo 24.
Its compatible amalgam supplies the literal E₄ and D₁₂ models in row (4).

The earlier source Theorems A/C remain explicit. Every F.6.18 model and
local-action premise is discharged; no classification input is assumed.
Source: Aschbacher–Smith F.6.18(1),(2),(4), printed pp.309–310.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
universe u
variable {κ : GroupClass.{u}} {D : Type u} [Group D] [Finite D] {G₁ G₂ : Subgroup D}

private noncomputable def primeFieldParameter (p : ℕ) (hp : p.Prime) : FieldParameter.{u} := by
  let : Fact p.Prime := ⟨hp⟩
  exact { Carrier := ULift.{u} (ZMod p)
          prime := p
          prime_isPrime := hp
          degree := 1
          degree_pos := by decide
          card := by simp }

private theorem four_of_prime_model
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (S : Sylow 2 D)
    (hS : G₁ ⊓ G₂ = (S : Subgroup D)) (hcard : Nat.card S = 4)
    (hcore : pCore 2 D = ⊥) (hF : generalizedFitting D = ⊤) (hQ : IsQuasisimple D)
    (p : ℕ) (hp : p.Prime) (h24 : p % 24 = 11 ∨ p % 24 = 13)
    (j : D ≃* PSL(2, ZMod p)) : Alternative G₁ G₂ S := by
  let : Fact p.Prime := ⟨hp⟩
  have hT : Nat.card (G₁ ⊓ G₂ : Subgroup D) = 4 := hS ▸ hcard
  obtain ⟨hE, hleft, hright⟩ := ChapterF.SourceAssembly.four_intersection_models h hcore hT
  let : IsElementaryAbelian 2 (G₁ ⊓ G₂ : Subgroup D) := hE
  let s := MulEquiv.subgroupCongr hS
  let : IsElementaryAbelian 2 S := IsElementaryAbelian.of_surjective s.toMonoidHom s.surjective
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour S := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  let : IsKleinFour E4 := ⟨by simp [E4, C], by simp [E4, C, Monoid.exponent_prod]⟩
  let : IsQuasisimple D := hQ
  let f := primeFieldParameter.{u} p hp
  let eF : ZMod p ≃+* f.Carrier := ULift.ringEquiv.symm
  exact Alternative.four f rfl h24 (j.trans (Atlas.fieldEquivPSL 2 eF)) hF
    (IsQuasisimple.of_mulEquiv ((MulEquiv.subgroupCongr hF).trans topEquiv).symm)
    IsKleinFour.nonempty_mulEquiv hleft hright


theorem quasisimple_four_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ D)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (S : Sylow 2 D)
    (hS : G₁ ⊓ G₂ = (S : Subgroup D)) (hcard : Nat.card S = 4)
    (hL : pResidual 2 D = generalizedFitting D ∧ IsQuasisimple (pResidual 2 D)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  have hT : Nat.card (G₁ ⊓ G₂ : Subgroup D) = 4 := hS ▸ hcard
  have hcore : pCore 2 D = ⊥ := le_bot_iff.mp
    (ChapterF.twoCore_le_primeToThreeCore.trans
      (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient q.equiv.symm).le)
  obtain ⟨hF, hQ, p, hp, h24, ⟨j⟩⟩ :=
    ChapterF.SourceAssembly.quasisimple_four_models (hA _) hC q.sqtk q.equiv.symm h hT hL
  exact four_of_prime_model h S hS hcard hcore hF hQ p hp h24 j


theorem small_sylow_source
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ D)
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂) (S : Sylow 2 D)
    (hS : G₁ ⊓ G₂ = (S : Subgroup D)) (hcard : Nat.card S ≤ 4) :
    Alternative G₁ G₂ S := by
  by_cases hc : IsCyclic (pCore 3 D)
  · let := q.coverGroup
    let := q.coverFinite
    have hgt := ChapterF.SourceAssembly.intersection_card_gt_two_of_cyclic_three_core
      q.equiv.symm h hc
    rw [hS] at hgt
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hn2 : n ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      exact hn ▸ hcard
    have hfour : Nat.card S = 4 := by
      interval_cases n
      · rw [hn] at hgt
        norm_num at hgt
      · rw [hn] at hgt
        norm_num at hgt
      · exact hn
    have hL := ChapterF.SourceAssembly.cyclic_four_quasisimple_source
      (hA _) q.sqtk q.equiv.symm h hc (hS ▸ hfour)
    exact quasisimple_four_source hA hC q h S hS hfour hL
  · exact noncyclic_source q h S hS hc
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
