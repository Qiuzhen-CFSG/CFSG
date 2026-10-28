module

public import Stellmacher.Recognition.SuzukiThreeSquareAction
import Mathlib.Tactic.Group

/-!
# Torus fusion for a centralizing point swap

If the point swap centralizes the two-point stabilizer, ambient conjugacy
between elements of this cyclic stabilizer is trivial. Inside a point
stabilizer this follows from the abelian quotient by the root group; outside
it follows by comparing the torus coordinates in the two Bruhat expressions.
In particular every subgroup of the torus has equal normalizer and centralizer.

This supplies the normalizer calculation in Suzuki (1965), Section II,
Lemmas 3 and 6, independently of the two transfer branches.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- A centralizing swap makes fusion between torus elements trivial. -/
public theorem twoPoint_eq_of_conj_of_swap_centralizes
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (k l : stabilizer (stabilizer G a) b) (x : G)
    (hconj : ((k : stabilizer G a) : G) * x =
      x * ((l : stabilizer G a) : G)) : k = l := by
  by_cases hx : x ∈ stabilizer G a
  · let xH : stabilizer G a := ⟨x, hx⟩
    have he : k.val * xH = xH * l.val := Subtype.ext hconj
    let : IsCyclic ((stabilizer G a) ⧸ Q) := h.quotient_cyclic
    have heq := congrArg (QuotientGroup.mk' Q) he
    simp only [map_mul] at heq
    have hkl : (QuotientGroup.mk' Q) k.val = (QuotientGroup.mk' Q) l.val := by
      rw [mul_comm' ((QuotientGroup.mk' Q) k.val)] at heq
      exact mul_left_cancel heq
    exact (Subgroup.isComplement_subgroup_right_iff_bijective.mp
      (h.root_complement b hb).symm).injective hkl
  · obtain ⟨u, m, v, hx'⟩ := h.exists_bruhat b hb t hta htb x hx
    let u' : Q := ⟨k.val * u.val * k.val⁻¹,
      (inferInstance : Q.Normal).conj_mem u.val u.property k.val⟩
    let v' : Q := ⟨l.val⁻¹ * v.val * l.val,
      (inferInstance : Q.Normal).conj_mem' v.val v.property l.val⟩
    have htl : t * ((l : stabilizer G a) : G) =
        ((l : stabilizer G a) : G) * t := by
      have he := congrArg (fun z : G => t * z) (htK l)
      simpa only [← mul_assoc, mul_inv_cancel, one_mul] using he.symm
    have he : (u', k * m, v) = (u, m * l, v') := by
      apply h.bruhat_injective b hb t hta htb
      change
        (((k : stabilizer G a) : G) * ((u : stabilizer G a) : G) *
          ((k : stabilizer G a) : G)⁻¹) *
          (((k : stabilizer G a) : G) * ((m : stabilizer G a) : G)) * t *
          ((v : stabilizer G a) : G) =
        ((u : stabilizer G a) : G) *
          (((m : stabilizer G a) : G) * ((l : stabilizer G a) : G)) * t *
          (((l : stabilizer G a) : G)⁻¹ * ((v : stabilizer G a) : G) *
            ((l : stabilizer G a) : G))
      calc
        _ = ((k : stabilizer G a) : G) * x := by rw [hx']; group
        _ = x * ((l : stabilizer G a) : G) := hconj
        _ = ((u : stabilizer G a) : G) * ((m : stabilizer G a) : G) *
            (t * ((l : stabilizer G a) : G)) *
            (((l : stabilizer G a) : G)⁻¹ * ((v : stabilizer G a) : G) *
              ((l : stabilizer G a) : G)) := by rw [hx']; group
        _ = _ := by rw [htl]; group
    have heK : k * m = m * l := congrArg (fun p => p.2.1) he
    let : IsCyclic (stabilizer (stabilizer G a) b) := h.twoPoint_cyclic b hb
    rw [mul_comm' k m] at heK
    exact mul_left_cancel heK

/-- Equivalent conjugacy-class formulation of torus fusion. -/
public theorem twoPoint_eq_of_isConj_of_swap_centralizes
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (k l : stabilizer (stabilizer G a) b)
    (hconj : IsConj ((k : stabilizer G a) : G) ((l : stabilizer G a) : G)) :
    k = l := by
  obtain ⟨x, hx⟩ := isConj_iff.mp hconj
  apply h.twoPoint_eq_of_conj_of_swap_centralizes b hb t hta htb htK k l x⁻¹
  calc
    _ = x⁻¹ * (x * ((k : stabilizer G a) : G) * x⁻¹) := by group
    _ = _ := by rw [hx]

/-- All subgroups of the torus have trivial normalizer action in the
centralizing-swap branch. -/
public theorem normalizer_eq_centralizer_of_le_twoPoint_of_swap_centralizes
    (b : Ω) (hb : b ≠ a) (t : G)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      t⁻¹ * ((k : stabilizer G a) : G) * t = ((k : stabilizer G a) : G))
    (R : Subgroup G)
    (hR : R ≤ stabilizer G a ⊓ stabilizer G b) :
    Subgroup.normalizer (R : Set G) = Subgroup.centralizer (R : Set G) := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro r hr
    have hxrx : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hx r).mp hr
    let k : stabilizer (stabilizer G a) b := ⟨⟨x * r * x⁻¹, (hR hxrx).1⟩,
      (hR hxrx).2⟩
    let l : stabilizer (stabilizer G a) b := ⟨⟨r, (hR hr).1⟩, (hR hr).2⟩
    have he := h.twoPoint_eq_of_conj_of_swap_centralizes b hb t hta htb htK k l x
      (by change (x * r * x⁻¹) * x = x * r; group)
    have hv : x * r * x⁻¹ = r := congrArg
      (fun z : stabilizer (stabilizer G a) b => ((z : stabilizer G a) : G)) he
    calc
      r * x = (x * r * x⁻¹) * x := by rw [hv]
      _ = x * r := by group
  · exact Subgroup.centralizer_le_normalizer (R : Set G)

end Stellmacher.Recognition.SuzukiThreeHypotheses
