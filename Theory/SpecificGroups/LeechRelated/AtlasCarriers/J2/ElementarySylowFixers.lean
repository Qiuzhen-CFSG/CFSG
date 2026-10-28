module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.PointwiseFixer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.SylowCenter
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order
public import Theory.GroupAction.SylowPointwiseInner
public import Theory.GroupAction.ElementarySylowFixerBound

/-!
# Elementary pointwise Sylow fixers of J₂

An automorphism fixing the marked Sylow subgroup centralizes the inner
image of its radical. The proved full radical-centralizer bound places it
inside that radical, so it is inner. Sylow conjugacy and the checked center
of order two give the elementary fixer bound for every Sylow subgroup.

This is an intrinsic calculation for the exact ATLAS degree-100 carrier,
used in Aschbacher–Smith, proof of 13.6.6, p.927. Its inputs retain the
ATLAS attribution and use no later source theorem.
-/

public section
open Subgroup
namespace Sporadic.LeechRelated.J2
open ExceptionalParabolics GeneratorPair
open ExceptionalParabolics.Seed ExceptionalParabolics.PairNormalizer

theorem automorphism_inner_of_fixes_sylow (S : Sylow 2 Carrier) (α : MulAut Carrier)
    (hfix : ∀ x ∈ S, α x = x) : ∃ g, α = MulAut.conj g := by
  have hbase (β : MulAut Carrier) (hβ : ∀ x ∈ Seed.s, β x = x) :
      ∃ x ∈ Seed.s, β = MulAut.conj x := by
    have hc : β ∈ centralizer (NormalizerAction.innerRadical : Set (MulAut Carrier)) := by
      rintro _ ⟨q, hq, rfl⟩
      apply MulEquiv.ext
      intro x
      change q * β x * q⁻¹ = β (q * x * q⁻¹)
      rw [map_mul, map_mul, map_inv, hβ q (q₂_le_s hq)]
    obtain ⟨q, hq, hqβ⟩ := NormalizerAction.radical_centralizer_le hc
    exact ⟨q, q₂_le_s hq, hqβ.symm⟩
  obtain ⟨g, _, hg⟩ := MulAut.fixing_inner_sylow
    (SecondParabolic.sylow FirstParabolic.card_l₁) S hbase α hfix
  exact ⟨g, hg⟩

theorem sylow_center_card_two (S : Sylow 2 Carrier) : Nat.card (center S) = 2 := by
  rw [Nat.card_congr (centerCongr
    (S.equiv (SecondParabolic.sylow FirstParabolic.card_l₁))).toEquiv]
  exact SecondParabolic.card_center_s

theorem elementary_sylow_fixer_card_le_two (hZ : center Carrier = ⊥)
    (S : Sylow 2 Carrier) (A : Subgroup (MulAut Carrier)) [IsElementaryAbelian 2 A]
    (hfix : ∀ α ∈ A, ∀ x ∈ S, α x = x) : Nat.card A ≤ 2 := by
  let : IsCyclic (center S) := isCyclic_of_card_dvd_prime (p := 2) (by
    rw [sylow_center_card_two])
  exact Theory.GroupAction.elementary_sylow_fixer_card_le_two_of_inner S hZ
    (fun α _ hα => automorphism_inner_of_fixes_sylow S α (fun x hx => hα ⟨x, hx⟩)) A hfix

end Sporadic.LeechRelated.J2
