module

public import Theory.SpecificGroups.Alternating.E9A4Words
public import Theory.GroupTheory.CentralCoprimeAbelianLift

/-!
# Local subgroups from two cubic lifts above E₉ × A₄

Suppose an E₉ × A₄ subgroup embeds in a quotient by a central three-group.
If the first cyclic generator and the A₄ three-cycle have commuting cubic
lifts, they generate an E₉ still faithful in the quotient. The normal Klein
four-group lifts through the coprime central kernel to a nontrivial
abelian two-group preserved by every lift of its normalizer. This constructs
both the two-subgroup and its normalizing E₉ explicitly from those inputs.

The cubic splitting hypotheses are essential and remain explicit here.
The O'Nan application supplies them using its actual linear word matrices.
Source: Aschbacher--Smith, A.2.19, printed p.41, and the E₉ × A₆ construction
in I.2.1, printed p.409. This lemma proves no arbitrary central extension
splits over E₉ × A₄.
-/

namespace Theory.SpecificGroups.E9A4
open Subgroup

private def cubicHom {G : Type*} [Group G] (x : G) (hx : x ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun a := x ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change x ^ (a.toAdd + b.toAdd).val = x ^ a.toAdd.val * x ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    have hmod (n : ℕ) : x ^ (n % 3) = x ^ n := by
      conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, hx, one_pow, mul_one]
    exact hmod _

private def cubicPair {G : Type*} [Group G] (x t : G)
    (hx : x ^ 3 = 1) (ht : t ^ 3 = 1) (hxt : Commute x t) :
    Multiplicative (ZMod 3 × ZMod 3) →* G where
  toFun a := cubicHom x hx (Multiplicative.ofAdd a.toAdd.1) *
    cubicHom t ht (Multiplicative.ofAdd a.toAdd.2)
  map_one' := by simp
  map_mul' a b := by
    change cubicHom x hx (Multiplicative.ofAdd a.toAdd.1 * Multiplicative.ofAdd b.toAdd.1) *
      cubicHom t ht (Multiplicative.ofAdd a.toAdd.2 * Multiplicative.ofAdd b.toAdd.2) = _
    rw [map_mul, map_mul]
    exact (hxt.pow_pow b.toAdd.1.val a.toAdd.2.val).mul_mul_mul_comm _ _

private def markedPair : Multiplicative (ZMod 3 × ZMod 3) →* Source :=
  cubicPair (generators 0) (generators 3) (by decide +kernel)
    (by decide +kernel) (by change _ * _ = _ * _; decide +kernel)

private theorem markedPair_injective : Function.Injective markedPair := by decide +kernel

private def fourGroup : Subgroup Source :=
  (⊥ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))).prod
    (alternatingGroup.kleinFour (Fin 4))

private theorem fourGroup_properties :
    fourGroup.Normal ∧ IsMulCommutative fourGroup ∧
      fourGroup ≠ ⊥ ∧ IsPGroup 2 fourGroup := by
  let K := alternatingGroup.kleinFour (Fin 4)
  let : K.Normal := alternatingGroup.normal_kleinFour (by simp)
  let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (by simp)
  let : IsMulCommutative K := IsKleinFour.isMulCommutative
  have hc : Nat.card fourGroup = 4 := by
    rw [fourGroup, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_bot, one_mul]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hN : fourGroup.Normal := by
    change ((⊥ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))).prod K).Normal
    infer_instance
  have hA : IsMulCommutative fourGroup := by
    change IsMulCommutative ((⊥ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))).prod K)
    let e := Subgroup.prodEquiv
      (⊥ : Subgroup (Multiplicative (ZMod 3 × ZMod 3))) K
    refine ⟨⟨fun a b => e.injective ?_⟩⟩
    rw [map_mul, map_mul]
    exact mul_comm' _ _
  refine ⟨hN, hA, ?_, IsPGroup.of_card (n := 2) hc⟩
  intro h
  rw [h, Subgroup.card_bot] at hc
  contradiction

/-- Commuting order-three lifts of the first cyclic factor and the marked
three-cycle give a faithful E9 in the normalizer of a lifted four-group. -/
public theorem local_lift_of_commuting_cubic_lifts
    {G H : Type*} [Group G] [Finite G] [Group H]
    (π : G →* H) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center G) (hker : IsPGroup 3 π.ker)
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
  have hcop : Nat.Coprime 2 (Nat.card π.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hker
    rw [hn]
    exact (show Nat.Coprime 2 3 by decide).pow_right n
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
