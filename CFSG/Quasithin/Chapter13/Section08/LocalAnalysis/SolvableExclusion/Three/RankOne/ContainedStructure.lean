module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints

/-!
# The proper contained L₁* in the Frattini subgroup

An invariant proper subgroup of a finite group with irreducible Frattini
quotient lies in the Frattini subgroup: otherwise it generates the whole
group modulo Frattini, hence generates the whole group. Apply this to L₁*
inside P*. Nontriviality rules out both abelian alternatives in ReducedOdd.
The remaining group is extraspecial of order 27, and its center of order
three must equal the nontrivial L₁*.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951, the contained-L₁* paragraph.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]

private theorem invariant_proper_le_frattini [Finite G]
    (P E R : Subgroup G) [P.Normal]
    (hirr : ∀ D : Subgroup G, (frattini P).map P.subtype ≤ D → D ≤ P →
      E ≤ normalizer (D : Set G) → D = (frattini P).map P.subtype ∨ D = P)
    (hRP : R < P) (hn : E ≤ normalizer (R : Set G)) :
    R ≤ (frattini P).map P.subtype := by
  let Phi := (frattini P).map P.subtype
  let : Phi.Normal := ConjAct.normal_of_characteristic_of_normal
  have hnorm : E ≤ normalizer ((R ⊔ Phi : Subgroup G) : Set G) :=
    (le_inf hn le_normalizer_of_normal).trans (normalizer_inf_normalizer_le_normalizer_sup R Phi)
  rcases hirr (R ⊔ Phi) le_sup_right (sup_le hRP.le (map_subtype_le _)) hnorm with h | h
  · exact h ▸ le_sup_left
  · have ht : R.subgroupOf P ⊔ frattini P = ⊤ := by
      apply map_injective P.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hRP.le,
        ← MonoidHom.range_eq_map, range_subtype]
      exact h
    have htop := congrArg (map P.subtype) (frattini_nongenerating ht)
    rw [map_subgroupOf_eq_of_le hRP.le, ← MonoidHom.range_eq_map, range_subtype] at htop
    exact (hRP.ne htop).elim

/-- A proper L₁* inside P* must lie in its Frattini subgroup. -/
theorem contained_le_frattini [Finite G] {p : ℕ} {H L₁ T M Vα : Subgroup G}
    (d : ReducedOdd p H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hTL : T ≤ normalizer (L₁ : Set G)) :
    Source.starImage H L₁ ≤ starFrattini H d.P := by
  let := d.Pstar_normal
  exact invariant_proper_le_frattini _ _ _ d.irreducible hlt
    (starImage_normalizes H (sup_le L₁.le_normalizer hTL))

/-- Both abelian alternatives are excluded by the actual Frattini interval. -/
theorem contained_extraspecial [Finite G] {H L₁ T M Vα : Subgroup G}
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hne : Source.starImage H L₁ ≠ ⊥)
    (hTL : T ≤ normalizer (L₁ : Set G)) :
    IsExtraspecial 3 (Source.starImage H d.P) ∧
      Nat.card (Source.starImage H d.P) = 3 ^ 3 ∧
      ∀ x : Source.starImage H d.P, x ^ 3 = 1 := by
  rcases d.Pstar_small with hc | ⟨hel, _⟩ | he
  · have hd := card_dvd_of_le hlt.le
    rw [hc] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact (hne (card_eq_one.mp h1)).elim
    · exact (hlt.ne (eq_of_le_of_card_ge hlt.le (by rw [hc, h3]))).elim
  · let := hel
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let : Fact (IsPGroup 3 (Source.starImage H d.P)) :=
      ⟨starImage_isPGroup H d.P d.P_isPGroup⟩
    have hh := contained_le_frattini d hlt hTL
    unfold starFrattini at hh
    rw [frattini_eq_bot_of_isElementaryAbelian (p := 3), Subgroup.map_bot] at hh
    exact (hne (bot_unique hh)).elim
  · exact he

/-- In the contained branch the nontrivial L₁* is exactly Z(P*). -/
theorem contained_center [Finite G] {H L₁ T M Vα : Subgroup G}
    (d : ReducedOdd 3 H L₁ T M Vα)
    (hlt : Source.starImage H L₁ < Source.starImage H d.P)
    (hne : Source.starImage H L₁ ≠ ⊥)
    (hTL : T ≤ normalizer (L₁ : Set G)) :
    Source.starImage H L₁ =
      (center (Source.starImage H d.P)).map (Source.starImage H d.P).subtype := by
  let := (contained_extraspecial d hlt hne hTL).1
  have hle := contained_le_frattini d hlt hTL
  unfold starFrattini at hle
  rw [IsExtraspecial.frattini_eq_center_three] at hle
  have hcard : Nat.card ((center (Source.starImage H d.P)).map
      (Source.starImage H d.P).subtype) = 3 := by
    rw [card_map_of_injective (Source.starImage H d.P).subtype_injective]
    exact IsExtraspecial.center_order_p 3 _
  have hd := card_dvd_of_le hle
  rw [hcard] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact (hne (card_eq_one.mp h1)).elim
  · exact eq_of_le_of_card_ge hle (by rw [hcard, h3])

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
