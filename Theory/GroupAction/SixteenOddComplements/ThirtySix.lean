module

public import Theory.GroupAction.SixteenOddComplements.Nine
public import Theory.GroupTheory.SmallIndexSolvable
public import Theory.GroupTheory.SolvableThreePartCore

/-!
# Reduced order-thirty-six actions on an elementary sixteen

A group of order 36 is solvable because its Sylow three-subgroup has
index four. If its two-core is trivial, the Fitting argument forces its
three-core to have order nine. An elementary four-subgroup complements
this normal nine. The existing faithful degree-four recognition therefore
identifies the group with S₃ × S₃.

Source application: Aschbacher--Smith F.5.4(4), printed p.301. This replaces
a general subgroup classification of GL₄(2) by the exact order and action
information supplied by the original normalizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace SixteenOddComplements
variable {G : Type*} [Group G] [Finite G]

theorem solvable_of_card_thirty_six (hc : Nat.card G = 36) : Group.IsSolvable G := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 G := default
  have hS : Nat.card S = 9 := by
    rw [S.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (S : Subgroup G).index = 4 := by
    have hh := (S : Subgroup G).card_mul_index
    rw [hS,hc] at hh
    omega
  let : Group.IsNilpotent S := S.isPGroup'.isNilpotent
  exact (S : Subgroup G).isSolvable_of_index_le_four hi.le

theorem threeCore_card_of_reduced_thirty_six (hc : Nat.card G = 36)
    (hcore : pCore 2 G = ⊥) : Nat.card (pCore 3 G) = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let S : Sylow 3 G := default
  have hS : Nat.card S = 9 := by
    rw [S.card_eq_multiplicity,hc]
    decide +kernel
  have hd : Nat.card (pCore 3 G) ∣ 3^2 := by
    change Nat.card (pCore 3 G) ∣ 9
    rw [← hS]
    exact card_dvd_of_le (pCore_isPGroup.le_sylow_of_normal S)
  have hlarge : ¬ Nat.card (pCore 3 G) ≤ 3 := by
    intro hsmall
    apply twoCore_ne_bot_of_solvable_threeCore_le_three
      (solvable_of_card_thirty_six hc) ?_ hsmall (hc ▸ (by decide)) hcore
    intro p hp hdiv
    have hd' : p ∣ 2^2*3^2 := by simpa [hc] using hdiv
    rcases hp.dvd_mul.mp hd' with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  have hn2 : n = 2 := by
    by_contra hh
    have hn1 : n ≤ 1 := by omega
    apply hlarge
    rw [he]
    exact (Nat.pow_le_pow_right (by decide : 0 < 3) hn1).trans (by decide)
  simpa [hn2] using he

/-- The actual faithful actor of order36 is S₃ × S₃ when its two-core is
trivial and its Sylow four-subgroup is elementary. -/
theorem equiv_of_reduced_thirty_six
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (f : G →* MulAut V) (hf : Function.Injective f)
    (hc : Nat.card G = 36) (hcore : pCore 2 G = ⊥)
    (P : Subgroup G) [IsElementaryAbelian 2 P] (hP : Nat.card P = 4) :
    Nonempty (G ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let J := (pCore 3 G).map e.toMonoidHom
  let P' := P.map e.toMonoidHom
  let : J.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 P' := IsElementaryAbelian.map _
  have hJ : Nat.card J = 9 := by
    exact (card_map_of_injective e.injective).trans (threeCore_card_of_reduced_thirty_six hc hcore)
  have hP' : Nat.card P' = 4 := (card_map_of_injective e.injective).trans hP
  have hcomp : J.IsComplement' P' := isComplement'_of_card_mul_and_disjoint
    (by rw [hJ,hP',← Nat.card_congr e.toEquiv,hc])
    (disjoint_of_coprime_natCard (by rw [hJ,hP'];decide))
  obtain ⟨d⟩ := equiv_of_normal_nine_four hV f.range J hJ P' hP' hcomp
  exact ⟨e.trans d⟩

end SixteenOddComplements
