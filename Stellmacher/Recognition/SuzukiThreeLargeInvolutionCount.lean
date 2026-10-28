module

public import Stellmacher.Recognition.SuzukiThreeCentralizerCount

/-!
# Involutions in the large Suzuki cell

When an involutory point swap centralizes the two-point stabilizer, the
involutions outside the point stabilizer have unique coordinates `u k t u⁻¹`,
where `u` belongs to the root group and `k² = 1` in the torus. The cyclic
torus of order eight has two such elements, giving exactly `27 * 2 = 54`
involutions. The large cell does not contain the identity.

Source: Suzuki (1965), Section II, Lemmas 1–3.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

private theorem twoPoint_square_one_card (b : Ω) (hb : b ≠ a) :
    Nat.card {k : stabilizer (stabilizer G a) b // k ^ 2 = 1} = 2 := by
  classical
  let T := stabilizer (stabilizer G a) b
  let : Finite T := Nat.finite_of_card_ne_zero (by
    rw [h.twoPoint_card b hb]
    decide)
  let : Fintype T := Fintype.ofFinite T
  let : IsCyclic T := h.twoPoint_cyclic b hb
  obtain ⟨j, hj⟩ := exists_prime_orderOf_dvd_card' 2 (G := T) (by
    rw [h.twoPoint_card b hb]
    decide)
  have hjpow : j ^ 2 = 1 := by rw [← hj]; exact pow_orderOf_eq_one j
  have hjne : j ≠ 1 := by intro he; simp [he] at hj
  have hlo : 2 ≤ (Finset.univ.filter (fun k : T => k ^ 2 = 1)).card := by
    have hsub : ({1, j} : Finset T) ⊆ Finset.univ.filter (fun k : T => k ^ 2 = 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> simp [hjpow]
    simpa [hjne.symm] using Finset.card_le_card hsub
  have hhi := IsCyclic.card_pow_eq_one_le (α := T) (n := 2) (by decide)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Nat.le_antisymm hhi hlo

/-- There are exactly 54 involutions outside the point stabilizer when the
involutory point swap centralizes the torus. -/
public theorem large_involution_card_of_centralizing_swap
    (b : Ω) (hb : b ≠ a) (t : G) (ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (hcentral : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G)) :
    Nat.card {x : G // orderOf x = 2 ∧ x ∉ stabilizer G a} = 54 := by
  let T := stabilizer (stabilizer G a) b
  have hcomm (k : T) : Commute ((k : stabilizer G a) : G) t := by
    change _ * t = t * _
    calc
      _ = t * (t⁻¹ * ((k : stabilizer G a) : G) * t) := by group
      _ = _ := by rw [hcentral k]
  have hsq (k : T) : (((k : stabilizer G a) : G) * t) ^ 2 = 1 ↔ k ^ 2 = 1 := by
    rw [(hcomm k).mul_pow, ht, mul_one]
    constructor
    · intro hk
      exact Subtype.ext (Subtype.ext hk)
    · intro hk
      exact congrArg (fun k : T => ((k : stabilizer G a) : G)) hk
  let f : (Q × {k : T // k ^ 2 = 1}) →
      {x : G // orderOf x = 2 ∧ x ∉ stabilizer G a} := fun p =>
    ⟨((p.1 : stabilizer G a) : G) * ((p.2.val : stabilizer G a) : G) * t *
        (((p.1⁻¹ : Q) : stabilizer G a) : G), by
      have hout := bruhat_not_mem_stabilizer b hb t hta p.1 p.2.val p.1⁻¹
      refine ⟨orderOf_eq_prime_iff.mpr ⟨?_, ?_⟩, hout⟩
      · exact (h.bruhat_sq_eq_one_iff b hb t hta htb p.1 p.2.val p.1⁻¹).mpr
          ⟨rfl, (hsq p.2.val).mpr p.2.property⟩
      · intro he
        exact hout (he ▸ (stabilizer G a).one_mem)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨u, k⟩ ⟨v, l⟩ he
      have hcoords : (u, k.val, u⁻¹) = (v, l.val, v⁻¹) :=
        h.bruhat_injective b hb t hta htb (congrArg Subtype.val he)
      have hu : u = v := congrArg Prod.fst hcoords
      have hk : k.val = l.val := congrArg (fun p => p.2.1) hcoords
      exact Prod.ext hu (Subtype.ext hk)
    · intro x
      obtain ⟨u, k, v, hx⟩ := h.exists_bruhat b hb t hta htb x.val x.property.2
      have hxpow : x.val ^ 2 = 1 := (orderOf_eq_prime_iff.mp x.property.1).1
      rw [hx] at hxpow
      obtain ⟨hv, hk⟩ := (h.bruhat_sq_eq_one_iff b hb t hta htb u k v).mp hxpow
      refine ⟨(u, ⟨k, (hsq k).mp hk⟩), Subtype.ext ?_⟩
      change _ * _ * t * _ = x.val
      rw [hx, hv]
  calc
    _ = Nat.card (Q × {k : T // k ^ 2 = 1}) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    _ = 54 := by rw [Nat.card_prod, h.root_card, h.twoPoint_square_one_card b hb]

end Stellmacher.Recognition.SuzukiThreeHypotheses
