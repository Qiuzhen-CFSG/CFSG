module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

/-!
# Subgroups cyclic modulo an elementary layer

A subgroup contained in ⟨b,E⟩, with E in the second center, has derived
subgroup contained in the center. If that center has order two and the
subgroup is nonabelian, its derived subgroup is the whole center.

If instead the subgroup is abelian, E is elementary at two, and b is an
element of order four in the subgroup, its square subgroup has order two.
Every square is a power of b², and b² itself is a square.

These are the intrinsic deductions following the cyclic quotient computation
in Parrott, *A characterization of the Tits' simple group* (1972), p.677.
-/

open scoped commutatorElement IsMulCommutative

namespace Subgroup

/-- A cyclic supplement to a subgroup of the second center has central
derived subgroup. -/
public theorem derived_le_center_of_le_zpowers_sup
    {G : Type*} [Group G] (L E : Subgroup G) (b : G)
    (hE : E ≤ upperCentralSeries G 2) (hL : L ≤ zpowers b ⊔ E) :
    (_root_.commutator L).map L.subtype ≤ center G := by
  let q := QuotientGroup.mk' (center G)
  have hEq : E.map q ≤ center (G ⧸ center G) := by
    rintro _ ⟨e, he, rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center G) x
    have hc : ⁅e, x⁆ ∈ center G := by
      simpa only [upperCentralSeries_one] using
        (mem_upperCentralSeries_succ_iff.mp (hE he) x)
    have hone : ⁅q e, q x⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hc
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  let B := zpowers (q b)
  let A := E.map q
  have hcomm : B ⊔ A ≤ centralizer ((B ⊔ A : Subgroup (G ⧸ center G)) : Set (G ⧸ center G)) := by
    apply sup_le
    · apply le_centralizer_iff.mpr
      exact sup_le B.le_centralizer (hEq.trans (center_le_centralizer _))
    · exact hEq.trans (center_le_centralizer _)
  have hLq : L.map q ≤ B ⊔ A := by
    simpa only [map_sup, MonoidHom.map_zpowers] using map_mono (f := q) hL
  have hzero : ⁅L.map q, L.map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hLq.trans (hcomm.trans (centralizer_le hLq)))
  rw [map_subtype_commutator, ← QuotientGroup.ker_mk' (center G), ← map_eq_bot_iff,
    map_commutator]
  exact hzero

/-- A nonabelian subgroup with a cyclic supplement to the second center
has derived image equal to the center when that center has order two. -/
public theorem derived_eq_center_of_injective_range_le_zpowers_sup
    {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
    (f : D →* G) (hf : Function.Injective f) (E : Subgroup G) (b : G)
    (hE : E ≤ upperCentralSeries G 2) (hL : f.range ≤ zpowers b ⊔ E)
    (hcenter : Nat.card (center G) = 2) (hnonabelian : ¬ IsMulCommutative D) :
    (_root_.commutator D).map f = center G := by
  have hle : (_root_.commutator D).map f ≤ center G := by
    rw [map_commutator_eq]
    have hh := derived_le_center_of_le_zpowers_sup f.range E b hE hL
    rwa [map_subtype_commutator] at hh
  have hdvd := card_dvd_of_le hle
  rw [hcenter, card_map_of_injective hf] at hdvd
  have hcard : Nat.card (_root_.commutator D) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hbot | htwo
    · exact (hnonabelian ((commutator_eq_bot_iff D).mp
        ((eq_bot_iff_card _).mpr hbot))).elim
    · exact htwo
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective hf, hcard, hcenter]

/-- An abelian subgroup generated modulo an elementary normal subgroup
by an element of order four has a square subgroup of order two. -/
public theorem square_card_two_of_injective_range_le_zpowers_sup
    {G D : Type*} [Group G] [Group D] [Finite D]
    (f : D →* G) (hf : Function.Injective f) (E : Subgroup G)
    [E.Normal] [IsElementaryAbelian 2 E] [IsMulCommutative D]
    (b : D) (hb : orderOf b = 4) (hL : f.range ≤ zpowers (f b) ⊔ E) :
    Nat.card (closure (Set.range (fun x : D => x ^ 2))) = 2 := by
  have hsquares : closure (Set.range (fun x : D => x ^ 2)) = zpowers (b ^ 2) := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro _ ⟨x, rfl⟩
      obtain ⟨c, hc, e, he, hcx⟩ := mem_sup_of_normal_right.mp (hL ⟨x, rfl⟩)
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hc
      let eD : D := b ^ (-n) * x
      have heD : f eD = e := by
        change f (b ^ (-n) * x) = e
        rw [map_mul, map_zpow, zpow_neg]
        rw [← hcx]
        group
      have he2 : eD ^ 2 = 1 := by
        apply hf
        rw [map_pow, heD, map_one]
        exact elemPow_eq_one_of_isElementaryAbelian (p := 2) e he
      have hx : x = b ^ n * eD := by
        dsimp only [eD]
        rw [zpow_neg]
        group
      change x ^ 2 ∈ zpowers (b ^ 2)
      have hp : (b ^ n) ^ 2 = (b ^ 2) ^ n := by
        rw [← zpow_natCast (b ^ n) 2, ← zpow_mul, zpow_mul', zpow_natCast]
      rw [hx, mul_pow, he2, mul_one, hp]
      exact zpow_mem_zpowers _ _
    · exact zpowers_le.mpr (subset_closure ⟨b, rfl⟩)
  rw [hsquares, Nat.card_zpowers, orderOf_pow, hb]
  decide

end Subgroup
