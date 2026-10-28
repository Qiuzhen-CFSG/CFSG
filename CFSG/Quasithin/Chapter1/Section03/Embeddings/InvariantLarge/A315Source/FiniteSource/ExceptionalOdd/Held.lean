module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.A315Source.FiniteSource.ExceptionalOdd.LocalCover
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue

/-!
# Held has no full Sylow pair at five or seven

The actual product has a nontrivial two-core. The intrinsic Sylow catalogue
places its maximal two-local overgroup in one of the literal max3, max4 or
max5 normalizers. The first two have a two-core quotient of order dividing
3 times the order of S6, while max5 has checked order 21504. These orders
exclude both required prime-square divisors.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
open Held Held.TwoLocalCandidates Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

private theorem held_local_quotient_card_dvd (i : Bool) : Nat.card (LocalQuotient i) ∣ 2160 := by
  let f := SixPoint.quotientAction i
  have hc := f.ker.card_mul_index
  rw [index_ker] at hc
  rw [← hc]
  have hd : Nat.card f.range ∣ 720 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using f.range.card_subgroup_dvd_card
  exact Nat.mul_dvd_mul (ThreeCoreBounds.quotientAction_kernel_card_dvd_three i) hd

private theorem held_max34_not_square {p : ℕ} (hp : p = 5 ∨ p = 7) (i : Bool) :
    ¬ p ^ 2 ∣ Nat.card (localOvergroup i) := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := localOvergroup i)).exists_card_eq
  have hcop : Nat.Coprime (p ^ 2) (Nat.card (pCore 2 (localOvergroup i))) := by
    rw [hn]
    have hh : Nat.Coprime (p ^ 2) 2 := by rcases hp with rfl | rfl <;> decide
    exact hh.pow_right n
  intro hd
  have hc := (pCore 2 (localOvergroup i)).card_mul_index
  rw [← hc] at hd
  have hh := (hcop.dvd_of_dvd_mul_left hd).trans (held_local_quotient_card_dvd i)
  rcases hp with rfl | rfl <;> norm_num at hh

theorem held_local_not_square {p : ℕ} (hp : p = 5 ∨ p = 7) (i : Fin 3) :
    ¬ p ^ 2 ∣ Nat.card (subgroup i) := by
  fin_cases i
  · exact held_max34_not_square hp false
  · exact held_max34_not_square hp true
  · change ¬ p ^ 2 ∣ Nat.card max5
    rw [Held.InvolutionFixedData.TwoB.max5_card]
    rcases hp with rfl | rfl <;> decide

theorem held_sylow_two_power_dvd (S : Sylow 2 Held.He) : 256 ∣ Nat.card S := by
  open Held.LocalPairs.SylowGeometry.Calculations in
    obtain ⟨T,hT⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  have hl : 1024 ≤ Nat.card S := by
    rw [Nat.card_congr (S.equiv T).toEquiv, hT]
    exact Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
      Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
  obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
  have h8 : 8 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (by decide : 2 ^ 8 ≤ 1024).trans (hn ▸ hl)
  rw [hn]
  exact pow_dvd_pow 2 h8

theorem held_no_pair {p : ℕ} [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    (B : Subgroup Held.He) (S : Sylow 2 Held.He) (hB : XiOddQuotient p B)
    (hperm : (B : Set Held.He) * (S : Set Held.He) = (S : Set Held.He) * (B : Set Held.He)) : False := by
  obtain ⟨T,hcatalogue⟩ := MaximalNormalizerCatalogue.exists_sylow_catalogue
  apply no_exceptional_pair_of_local_cover (hp.imp_right Or.inl) T (held_sylow_two_power_dvd T) _ B S hB hperm
  intro M hM hTM
  obtain ⟨R,hR,hn,he,hRM⟩ := exists_normal_elementary_normalizer_of_sylow_le T hM hTM
  obtain ⟨i,g,hg⟩ := hcatalogue R hR hn he (hRM ▸ hM)
  rw [hRM, hg, card_map_of_injective (MulAut.conj g).injective]
  exact held_local_not_square hp i

variable {κ : GroupClass} {J : Type*} [Group J] [Finite J]
    {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}

theorem not_held (hp : p = 5 ∨ p = 7)
    (hA : OddCartan.AmbientInput κ D B S p)
    (hB : SourceTransport.PairAction p (S : Subgroup J) B)
    (e : D ≃* Held.He) : False := by
  let : Fact p.Prime := ⟨hA.prime⟩
  let : D.Normal := hA.normal
  obtain ⟨U,_,hU,hperm⟩ := exists_model_sylow_pair S hA.inside hB.oddComplement hA.permutes e
  exact held_no_pair hp _ U hU hperm
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.A315Source.ExceptionalOdd
