module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.GraphField.Cover.Frattini
/-!
# The centralizing action alternative

An element of Lᵣ that normalizes C_T(E) must commute with C_Q(E): its
commutators lie in both an odd group and T. Irreducibility then makes
such an element trivial. Transitivity on E minus the identity supplies
an element of order three in Y by orbit–stabilizer and Cauchy's theorem.
It is therefore outside Lᵣ. When Y centralizes Lᵣ this is precisely the
independent actor excluded by quasithinness in Endgame.

The position C_Q(E) ≤ T is explicit; choosing the normalizer model in
that position remains a separate Sylow-conjugacy obligation.

Source: Aschbacher–Smith, proof of 16.4.9(2), printed p.1191.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.GraphField
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {r z : G} {L : Subgroup G}

omit [Finite G] in
/-- The residual meets the actual simultaneous normalizer trivially. -/
theorem residual_disjoint_coverNormalizer
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hplace : d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ (T : Subgroup G)) :
    Disjoint (residual L r) (coverNormalizer T r z) := by
  let D := residual L r
  let C := (T : Subgroup G) ⊓ centralizer (fourGroup r z : Set G)
  let : IsElementaryAbelian 3 D := hD
  have hdis : Disjoint D (T : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 3 D).disjoint_of_coprime T.isPGroup' (by decide)
  apply disjoint_def.mpr
  intro x hxD hxN
  have hfix : d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ centralizer ({x} : Set G) := by
    intro a ha
    have haC : a ∈ C := ⟨hplace ha, ha.2⟩
    have hxC : x * a * x⁻¹ ∈ C := (mem_normalizer_iff.mp hxN.2 a).mp haC
    have hmT : x * a * x⁻¹ * a⁻¹ ∈ (T : Subgroup G) :=
      (T : Subgroup G).mul_mem hxC.1 ((T : Subgroup G).inv_mem (hplace ha))
    have haD : a * x⁻¹ * a⁻¹ ∈ D :=
      (mem_normalizer_iff.mp (d.normalizes_residual ha.1) x⁻¹).mp (D.inv_mem hxD)
    have hmD : x * a * x⁻¹ * a⁻¹ ∈ D := by
      simpa only [mul_assoc] using D.mul_mem hxD haD
    have hm := disjoint_def.mp hdis hmD hmT
    apply mem_centralizer_singleton_iff.mpr
    have he : (x * a) * (a * x)⁻¹ = 1 := by
      simpa only [mul_inv_rev, mul_assoc] using hm
    exact (mul_inv_eq_one.mp he).symm
  have hn : d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ normalizer (zpowers x : Set G) := by
    have hc : centralizer ({x} : Set G) = centralizer (zpowers x : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact hfix.trans (hc ▸ centralizer_le_normalizer (zpowers x : Set G))
  rcases c.irreducible (zpowers x) (zpowers_le.mpr hxD) hn with hbot | he
  · exact zpowers_eq_bot.mp hbot
  · have hc : orderOf x = 9 := by
      have hh := congrArg (fun K : Subgroup G => Nat.card K) he
      simpa only [Nat.card_zpowers, h9] using hh
    have hx3 : x ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian x hxD
    have hd := orderOf_dvd_of_pow_eq_one hx3
    rw [hc] at hd
    norm_num at hd

/-- Transitivity on the four-group forces a genuine element of order three in Y. -/
theorem coverY_exists_order_three
    (hcard : Nat.card (fourGroup r z) = 4) (hz : z ≠ 1)
    (htrans : CoverTransitive T r z) : ∃ x ∈ coverY T r z, orderOf x = 3 := by
  classical
  let E := fourGroup r z
  let Y := coverY T r z
  let f : Y →* MulAut E := E.normalizerMonoidHom.comp (inclusion (coverY_le_normalizer T r z))
  let K := f.range
  let zE : E := ⟨z, mem_sup_right (mem_zpowers z)⟩
  have horbit : MulAction.orbit K zE = ({1} : Set E)ᶜ := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩ hx
      have hh : (k : MulAut E) zE = 1 := hx
      have hze : zE = 1 := (k : MulAut E).injective (hh.trans (map_one _).symm)
      exact hz (congrArg Subtype.val hze)
    · intro hx
      have hx1 : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
      obtain ⟨a, ha, he⟩ := htrans z zE.property hz x x.property hx1
      exact MulAction.mem_orbit_iff.mpr
        ⟨⟨f ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩⟩, Subtype.ext he⟩
  have hc : Nat.card (MulAction.orbit K zE) = 3 := by
    rw [horbit]
    change (({1} : Set E)ᶜ).ncard = 3
    rw [Set.ncard_compl, Set.ncard_singleton, hcard]
  have hd : 3 ∣ Nat.card K := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K zE)
    rw [Nat.card_prod, hc] at hh
    exact ⟨Nat.card (MulAction.stabilizer K zE), hh.symm⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (hd.trans (card_range_dvd f))
  exact ⟨x, x.property, (orderOf_coe x).trans hx⟩

/-- Construct the independent order-three actor in the centralizing alternative. -/
theorem independent_three_of_coverY_centralizes
    (d : NormalizerData L r z) (c : CoverActionData d)
    (hD : IsElementaryAbelian 3 (residual L r)) (h9 : Nat.card (residual L r) = 9)
    (hplace : d.Q ⊓ centralizer (fourGroup r z : Set G) ≤ (T : Subgroup G))
    (hcard : Nat.card (fourGroup r z) = 4) (hz : z ≠ 1)
    (htrans : CoverTransitive T r z)
    (hfix : coverY T r z ≤ centralizer (residual L r : Set G)) :
    ∃ x ∈ coverY T r z, orderOf x = 3 ∧ x ∉ residual L r ∧
      residual L r ≤ centralizer ({x} : Set G) := by
  obtain ⟨x, hx, hx3⟩ := coverY_exists_order_three hcard hz htrans
  refine ⟨x, hx, hx3, ?_, ?_⟩
  · intro hxD
    have he := disjoint_def.mp (residual_disjoint_coverNormalizer d c hD h9 hplace)
      hxD (map_subtype_le _ hx)
    simp [he] at hx3
  · intro a ha
    exact mem_centralizer_singleton_iff.mpr (hfix hx a ha)

end CFSG.Quasithin.Chapter16.Intersections.GraphField
