module
public import Theory.SpecificGroups.Alternating.E9A4CentralLift
import all Theory.SpecificGroups.Alternating.E9A4CentralLift

/-!
# The normal four-group lift through an odd central kernel

The coprime four-group construction only uses that the kernel has odd order.
We intentionally reuse the internal marked pair and normal four-group of the
parent module, retaining its literal E₉ × A₄ coordinates. This supplies the
local subgroup needed in the O'Nan case of Aschbacher–Smith A.2.19, printed p.41.
-/
namespace Theory.SpecificGroups.E9A4
open Subgroup

/-- Commuting cubic lifts above E₉ × A₄ normalize a nontrivial lifted
four-group whenever the central kernel has odd order. -/
public theorem local_lift_of_commuting_cubic_lifts_of_odd_kernel
    {G H : Type*} [Group G] [Finite G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center G) (hker : Odd (Nat.card π.ker))
    (j : Source →* H) (hj : Function.Injective j)
    (x t : G) (hx : x ^ 3 = 1) (ht : t ^ 3 = 1) (hxt : Commute x t)
    (hpx : π x = j (generators 0)) (hpt : π t = j (generators 3)) :
    ∃ (Q : Subgroup G) (f : Multiplicative (ZMod 3 × ZMod 3) →* G),
      Q ≠ ⊥ ∧ IsPGroup 2 Q ∧ Function.Injective (π.comp f) ∧
        ∀ a, f a ∈ normalizer (Q : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨hN, hA, hne, hp⟩ := fourGroup_properties
  let := hN
  let := hA
  let B := fourGroup.map j
  have hBp : IsPGroup 2 B := hp.map j
  have hBne : B ≠ ⊥ := fun h => hne ((fourGroup.map_eq_bot_iff_of_injective hj).mp h)
  have hcop : Nat.Coprime 2 (Nat.card π.ker) := hker.coprime_two_left
  obtain ⟨Q, hQp, _, hQB, hn⟩ :=
    exists_abelian_prime_lift_of_central_coprime_kernel π hπ hcentral hcop B hBp
  let f := cubicPair x t hx ht hxt
  have hfac : π.comp f = j.comp markedPair := by
    apply MonoidHom.ext
    intro a
    change π (x ^ a.toAdd.1.val * t ^ a.toAdd.2.val) =
      j ((generators 0) ^ a.toAdd.1.val * (generators 3) ^ a.toAdd.2.val)
    simp only [map_mul, map_pow, hpx, hpt]
  refine ⟨Q, f, ?_, hQp, ?_, ?_⟩
  · intro hQ
    apply hBne
    rw [← hQB, hQ, Subgroup.map_bot]
  · rw [hfac]
    exact hj.comp markedPair_injective
  · intro a
    apply hn
    change π (f a) ∈ normalizer (fourGroup.map j : Set H)
    rw [show π (f a) = j (markedPair a) from DFunLike.congr_fun hfac a]
    apply le_normalizer_map j
    exact mem_map.mpr ⟨markedPair a, by rw [fourGroup.normalizer_eq_top]; trivial, rfl⟩

end Theory.SpecificGroups.E9A4
