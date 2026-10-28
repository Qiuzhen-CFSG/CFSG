module

public import Stellmacher.Recognition.SuzukiThreeBruhat
public import Theory.GroupAction.EightPowerFixedPoint
public import Theory.GroupTheory.CyclicEightSquareHom
import Mathlib.Tactic.Group

/-!
# The two possible torus actions in degree 28

A torus element acts on the 27 root elements with order dividing eight. Its
square fixes a nonidentity root element by cycle counting. Suzuki's Lemma 2
then forces every point swap to centralize the torus squares. On a cyclic
group of order eight this leaves exactly the identity and fifth-power maps.

This specializes the preliminary steps of Suzuki (1965), Section II,
Lemmas 3–7, without using recognition or the structure of the root group.
Excluding the identity action is a separate transfer argument.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- All elements interchanging the two base points induce the same torus action. -/
public theorem swap_conj_independent (b : Ω) (hb : b ≠ a) (s t : G)
    (hsa : s • a = b) (hsb : s • b = a)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b) :
    s⁻¹ * ((k : stabilizer G a) : G) * s =
      t⁻¹ * ((k : stabilizer G a) : G) * t := by
  have htia : t⁻¹ • a = b := by rw [← htb, inv_smul_smul]
  have htib : t⁻¹ • b = a := by rw [← hta, inv_smul_smul]
  let z : stabilizer (stabilizer G a) b :=
    ⟨⟨s * t⁻¹, by simp only [mem_stabilizer_iff, mul_smul, htia, hsb]⟩,
      by change (s * t⁻¹) • b = b; rw [mul_smul, htib, hsa]⟩
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  have hcomm : ((k : stabilizer G a) : G) * (s * t⁻¹) =
      (s * t⁻¹) * ((k : stabilizer G a) : G) :=
    congrArg (fun l : stabilizer (stabilizer G a) b => ((l : stabilizer G a) : G))
      (mul_comm' k z)
  calc
    _ = t⁻¹ * (s * t⁻¹)⁻¹ * (((k : stabilizer G a) : G) * (s * t⁻¹)) * t := by group
    _ = _ := by rw [hcomm]; group

/-- Every torus square centralizes a nonidentity root element. -/
public theorem exists_root_ne_one_commute_square (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) :
    ∃ q : Q, q ≠ 1 ∧
      ((k : stabilizer G a) : G) ^ 2 * ((q : stabilizer G a) : G) =
        ((q : stabilizer G a) : G) * ((k : stabilizer G a) : G) ^ 2 := by
  classical
  let : Finite Q := Nat.finite_of_card_ne_zero (by rw [h.root_card]; decide)
  let : Fintype Q := Fintype.ofFinite Q
  let ρ : stabilizer (stabilizer G a) b →* Equiv.Perm Q :=
    ((MulAut.toPerm Q).comp (MulAut.conjNormal (H := Q))).comp
      (stabilizer (stabilizer G a) b).subtype
  have hk8 : k ^ 8 = 1 := by
    simpa only [h.twoPoint_card b hb] using (pow_card_eq_one' (x := k))
  have hf8 : (ρ k) ^ 8 = 1 := by rw [← map_pow, hk8, map_one]
  have hf1 : (ρ k) 1 = 1 := by
    change (MulAut.conjNormal (H := Q) k.val) 1 = 1
    exact map_one _
  obtain ⟨q, hq, he⟩ :=
    Equiv.Perm.exists_ne_sq_apply_eq_self_of_card_twentySeven
      (by simpa only [← Nat.card_eq_fintype_card] using h.root_card) (ρ k) hf8 1 hf1
  rw [← map_pow] at he
  have he' := congrArg (fun q : Q => ((q : stabilizer G a) : G)) he
  change ((k : stabilizer G a) : G) ^ 2 * ((q : stabilizer G a) : G) *
      (((k : stabilizer G a) : G) ^ 2)⁻¹ = ((q : stabilizer G a) : G) at he'
  refine ⟨q, hq, ?_⟩
  calc
    _ = (((k : stabilizer G a) : G) ^ 2 * ((q : stabilizer G a) : G) *
        (((k : stabilizer G a) : G) ^ 2)⁻¹) * ((k : stabilizer G a) : G) ^ 2 := by group
    _ = _ := by rw [he']

/-- Any element interchanging the two base points fixes every torus square. -/
public theorem swapConj_sq (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (k : stabilizer (stabilizer G a) b) :
    swapConj b t hta htb (k ^ 2) = k ^ 2 := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [swapConj_coe, Subgroup.coe_pow]
  by_contra he
  obtain ⟨q, hq, hcomm⟩ := h.exists_root_ne_one_commute_square b hb k
  exact hq (h.root_eq_one_of_commute_of_swap_conj_ne b hb t hta htb (k ^ 2) he q hcomm)

/-- A point swap induces either the identity or fifth-power map on the torus. -/
public theorem swap_conj_eq_self_or_pow_five (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a) :
    (∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G)) ∨
    (∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) ^ 5) := by
  let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
  rcases (swapConj b t hta htb).eq_id_or_pow_five_of_card_eight_of_sq_fixed
      (h.twoPoint_card b hb) (h.swapConj_sq b hb t hta htb) with hid | hfive
  · refine Or.inl (fun k => ?_)
    simpa only [swapConj_coe] using congrArg
      (fun l : stabilizer (stabilizer G a) b => ((l : stabilizer G a) : G)) (hid k)
  · refine Or.inr (fun k => ?_)
    simpa only [swapConj_coe, Subgroup.coe_pow] using congrArg
      (fun l : stabilizer (stabilizer G a) b => ((l : stabilizer G a) : G)) (hfive k)

/-- A nontrivial point-swap action is necessarily the fifth-power map. -/
public theorem swap_conj_eq_pow_five_of_ne (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (hne : ∃ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t ≠ ((k : stabilizer G a) : G)) :
    ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G) ^ 5 := by
  rcases h.swap_conj_eq_self_or_pow_five b hb t hta htb with hid | hfive
  · obtain ⟨k, hk⟩ := hne
    exact (hk (hid k)).elim
  · exact hfive

end Stellmacher.Recognition.SuzukiThreeHypotheses
