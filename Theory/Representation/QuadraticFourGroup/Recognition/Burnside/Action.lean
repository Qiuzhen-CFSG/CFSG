module

public import Theory.Representation.QuadraticFourGroup.Recognition.Spectrum
public import Theory.GroupAction.SylowCentralizerCardinality
public import Theory.GroupTheory.SylowCentralizerCounting
public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# The Sylow action under Burnside's element-order condition

Let `G` be finite, simple and perfect, with an involution, and suppose each
of its elements has order two or odd order. Its Sylow two-subgroups are
nonnormal elementary abelian groups of order `2^n`, with `n > 1`. Burnside
transfer excludes order two; the explicit involution excludes order one.

The full involution-centralizer equality proved in `Recognition.Spectrum`
lets us apply Suzuki's involution-coset count. It follows that a Sylow
subgroup acts regularly on all the other Sylow subgroups. We derive the
exact number of Sylow subgroups, faithfulness and double transitivity of
the ambient action, and the bound of two on nonidentity fixed sets.

This proves the action reduction, not the field coordinatization or the
identification with `PSL₂`.

Sources: W. Burnside, *On a Class of Groups of Finite Order*, Transactions
of the Cambridge Philosophical Society XVIII (1900), 269–276, §§1–3;
`refs/original/burnside-1900.pdf`. The counting route used here is Suzuki,
*Finite groups with nilpotent centralizers* (1961), Part I, Theorem 2,
printed pp. 428–432, `refs/original/suzuki-nilpotent.pdf`.
-/

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.InvolutionOddSpectrum
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] [Group.IsPerfect G]

omit [Finite G] in
private theorem card_ne_two : Nat.card G ≠ 2 := by
  intro h
  let : IsCyclic G := isCyclic_of_prime_card h
  exact Group.IsPerfect.not_isMulCommutative G inferInstance

private theorem sylow_card_ne_two (P : Sylow 2 G) : Nat.card P ≠ 2 := by
  intro hP
  have hdiv := P.centralizer_relIndex_normalizer_dvd_prime_sub_one hP
  have heq : (centralizer (P : Set G)).relIndex (normalizer (P : Set G)) = 1 := by
    simpa using Nat.eq_one_of_dvd_one hdiv
  exact P.centralizer_relIndex_normalizer_ne_one_of_simple hP card_ne_two heq

omit [IsSimpleGroup G] [Group.IsPerfect G] in
private theorem sylow_ne_bot (t : G) (ht : orderOf t = 2) (P : Sylow 2 G) :
    (P : Subgroup G) ≠ ⊥ := by
  intro h
  have hd := P.dvd_card_of_dvd_card (ht ▸ orderOf_dvd_natCard t)
  rw [h, card_bot] at hd
  exact Nat.prime_two.not_dvd_one hd

/-- A Sylow two-subgroup is proper and nonnormal in the simple perfect group. -/
public theorem sylow_not_normal (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P : Sylow 2 G) : ¬ (P : Subgroup G).Normal := by
  intro hn
  rcases hn.eq_bot_or_eq_top with hb | he
  · exact sylow_ne_bot t ht P hb
  · let : IsElementaryAbelian 2 P := (hG.subgroup P).elementaryAbelian P.isPGroup'
    have hcomm : IsMulCommutative (⊤ : Subgroup G) := he ▸ inferInstance
    apply Group.IsPerfect.not_isMulCommutative G
    exact ⟨⟨fun x y => congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x, mem_top x⟩ : (⊤ : Subgroup G)) ⟨y, mem_top y⟩)⟩⟩

/-- The elementary abelian Sylow subgroup contains two distinct involutions. -/
public theorem sylow_distinct_involutions (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P : Sylow 2 G) :
    ∃ u v : P, orderOf u = 2 ∧ orderOf v = 2 ∧ u ≠ v := by
  classical
  let : Nontrivial P := (P : Subgroup G).nontrivial_iff_ne_bot.mpr (sylow_ne_bot t ht P)
  let : IsElementaryAbelian 2 P := (hG.subgroup P).elementaryAbelian P.isPGroup'
  have hord (x : P) (hx : x ≠ 1) : orderOf x = 2 := by
    apply orderOf_eq_prime
    · exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
    · exact hx
  obtain ⟨u, hu⟩ := exists_ne (1 : P)
  by_contra h
  have hevery (v : P) : v = 1 ∨ v = u := by
    by_cases hv : v = 1
    · exact Or.inl hv
    · exact Or.inr (by
        by_contra hne
        exact h ⟨u, v, hord u hu, hord v hv, Ne.symm hne⟩)
  apply sylow_card_ne_two P
  apply Nat.card_eq_two_iff.mpr
  refine ⟨1, u, Ne.symm hu, ?_⟩
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  exact hevery v

/-- Conjugation by the chosen Sylow subgroup is regular on the other Sylow subgroups. -/
public theorem sylow_regular (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) (P : Sylow 2 G) :
    ∀ Q R : Sylow 2 G, Q ≠ P → R ≠ P → ∃! x : P, (x : G) • Q = R := by
  have hc : ∀ x ∈ (P : Subgroup G), x ≠ 1 → centralizer ({x} : Set G) ≤ P :=
    fun x hx hne => (hG.centralizer_eq_sylow P hx hne).le
  have hn := hG.sylow_not_normal t ht P
  have htwo := hG.sylow_distinct_involutions t ht P
  have htrans := P.transitive_of_centralizer_le_of_card_le hc
    (P.card_sylow_le_of_centralizer_le hn hc htwo)
  intro Q R hQ hR
  obtain ⟨x, hx⟩ := htrans Q R hQ hR
  refine ⟨x, hx, fun y hy => ?_⟩
  have he := P.eq_one_of_smul_eq_of_centralizer_le Q hc hQ (x⁻¹ * y) (by
    change ((x : G)⁻¹ * (y : G)) • Q = Q
    rw [mul_smul, hy, ← hx, inv_smul_smul])
  exact (inv_mul_eq_one.mp he).symm

/-- The explicit involution and perfect simplicity give the strict source parameter bound. -/
public theorem sylow_card (t : G) (ht : orderOf t = 2) (P : Sylow 2 G) :
    ∃ n : ℕ, 1 < n ∧ Nat.card P = 2 ^ n := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  refine ⟨n, ?_, hn⟩
  by_contra h
  have hnle : n ≤ 1 := by omega
  interval_cases n
  · have hbot : (P : Subgroup G) = ⊥ := Subgroup.card_eq_one.mp (by simpa using hn)
    exact sylow_ne_bot t ht P hbot
  · exact sylow_card_ne_two P (by simpa using hn)

/-- The conjugation action on the actual Sylow subgroups is faithful. -/
public theorem sylowAction_faithful (hG : InvolutionOddSpectrum G) (t : G) (ht : orderOf t = 2) :
    Function.Injective (MulAction.toPermHom G (Sylow 2 G)) := by
  let P : Sylow 2 G := Classical.choice Sylow.nonempty
  exact P.toPermHom_injective_of_centralizer_le (hG.sylow_not_normal t ht P)
    (fun _ hx hne => (hG.centralizer_eq_sylow P hx hne).le)

/-- No nonidentity element fixes three distinct Sylow two-subgroups. -/
public theorem sylowAction_at_most_two_fixed (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) :
    ∀ g : G, g ≠ 1 → ∀ P Q R : Sylow 2 G, P ≠ Q → P ≠ R → Q ≠ R →
      ¬ (g • P = P ∧ g • Q = Q ∧ g • R = R) := by
  let P : Sylow 2 G := Classical.choice Sylow.nonempty
  exact P.at_most_two_fixed_of_centralizer_le_of_transitive
    (fun _ hx hne => (hG.centralizer_eq_sylow P hx hne).le)
    (fun Q R hQ hR => (hG.sylow_regular t ht P Q R hQ hR).exists)

/-- There are exactly one more Sylow two-subgroups than elements of a Sylow subgroup. -/
public theorem card_sylow (hG : InvolutionOddSpectrum G) (t : G) (ht : orderOf t = 2)
    (P : Sylow 2 G) : Nat.card (Sylow 2 G) = Nat.card P + 1 := by
  classical
  obtain ⟨Q, hQ⟩ := P.exists_ne_of_not_normal (hG.sylow_not_normal t ht P)
  let f : P → {R : Sylow 2 G // R ≠ P} := fun x =>
    ⟨(x : G) • Q, by
      intro hx
      have hxP : (x : G) • P = P := Sylow.smul_eq_iff_mem_normalizer.mpr
        (le_normalizer x.property)
      exact hQ (smul_left_cancel (x : G) (hx.trans hxP.symm))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      obtain ⟨z, _, hz⟩ := hG.sylow_regular t ht P Q (f x) hQ (f x).property
      exact (hz x rfl).trans (hz y (congrArg Subtype.val hxy).symm).symm
    · intro R
      obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P Q R hQ R.property
      exact ⟨x, Subtype.ext hx⟩
  have heq := Nat.card_eq_of_bijective f hf
  let := Fintype.ofFinite (Sylow 2 G)
  have hcard : Nat.card {R : Sylow 2 G // R ≠ P} = Nat.card (Sylow 2 G) - 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [hcard] at heq
  have hp := Nat.card_pos (α := Sylow 2 G)
  change Nat.card P = Nat.card (Sylow 2 G) - 1 at heq
  omega

/-- The actual Sylow conjugation action is doubly transitive. -/
public theorem sylowAction_two_pretransitive (hG : InvolutionOddSpectrum G)
    (t : G) (ht : orderOf t = 2) :
    MulAction.IsMultiplyPretransitive G (Sylow 2 G) 2 := by
  let P : Sylow 2 G := Classical.choice Sylow.nonempty
  apply (SubMulAction.ofStabilizer.isMultiplyPretransitive (a := P)).mpr
  apply MulAction.is_one_pretransitive_iff.mpr
  refine ⟨fun Q R => ?_⟩
  obtain ⟨x, hx, _⟩ := hG.sylow_regular t ht P Q R Q.property R.property
  refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
  rw [Sylow.stabilizer_eq_normalizer]
  exact le_normalizer x.property
end Theory.GroupTheory.InvolutionOddSpectrum
