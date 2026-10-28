module

public import Theory.Representation.QuadraticFourGroup.Models

/-!
# Cubic dihedral fixed spaces

Two commuting rotations of order dividing three, each inverted by an
involution centralizing the other rotation, give the fixed-space assertion
of GLS, volume 2, Lemma 25.12(iii) for two dihedral factors of order six.
It suffices that the second involution fix displacements by the first.

Conjugating and multiplying displacements transfers this identity from the
involutions to the rotations. In characteristic two, a vector fixed by the
product must then be fixed by both rotations. These local calculations need
neither faithfulness nor irreducibility.
-/

@[expose] public section

namespace Representation.QuadraticFourGroup

section General
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

private theorem cross_mul {a b c : G}
    (ha : ∀ v, ρ c (ρ a v - v) = ρ a v - v)
    (hb : ∀ v, ρ c (ρ b v - v) = ρ b v - v) :
    ∀ v, ρ c (ρ (a * b) v - v) = ρ (a * b) v - v := by
  intro v
  have heq : ρ (a * b) v - v =
      (ρ a (ρ b v) - ρ b v) + (ρ b v - v) := by
    simp [map_mul, Module.End.mul_apply]
  rw [heq, map_add, ha, hb]

private theorem cross_conj {a c t : G} (ht : Commute t c)
    (ha : ∀ v, ρ c (ρ a v - v) = ρ a v - v) :
    ∀ v, ρ c (ρ (t * a * t⁻¹) v - v) = ρ (t * a * t⁻¹) v - v := by
  intro v
  have htc (w : V) : ρ c (ρ t w) = ρ t (ρ c w) :=
    congrArg (fun f : Module.End k V => f w) (ht.map ρ).eq.symm
  have hti (w : V) : ρ t (ρ t⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have heq : ρ (t * a * t⁻¹) v - v =
      ρ t (ρ a (ρ t⁻¹ v) - ρ t⁻¹ v) := by
    simp only [map_mul, Module.End.mul_apply, map_sub, hti]
  rw [heq, htc, ha]

private theorem cross_symm {a c : G} (hac : Commute a c)
    (ha : ∀ v, ρ c (ρ a v - v) = ρ a v - v) :
    ∀ v, ρ a (ρ c v - v) = ρ c v - v := by
  intro v
  have hv := ha v
  have hacv : ρ c (ρ a v) = ρ a (ρ c v) :=
    congrArg (fun f : Module.End k V => f v) (hac.map ρ).eq.symm
  simp only [map_sub, hacv] at hv ⊢
  exact sub_eq_iff_eq_add.mpr (by
    have := (sub_eq_iff_eq_add.mp hv)
    calc ρ a (ρ c v) = (ρ a v - v) + ρ c v := this
      _ = (ρ c v - v) + ρ a v := by abel)

private theorem cross_cubic {a c r : G} (ha : a * a = 1) (hr : r ^ 3 = 1)
    (har : a * r * a⁻¹ = r⁻¹) (hrc : Commute r c)
    (hac : ∀ v, ρ c (ρ a v - v) = ρ a v - v) :
    ∀ v, ρ c (ρ r v - v) = ρ r v - v := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hr2 : r * r = r⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa [pow_succ, pow_two] using hr)
  have heq : r⁻¹ * a * r * a = r := by
    calc r⁻¹ * a * r * a = r⁻¹ * (a * r * a⁻¹) := by rw [hainv]; group
      _ = r⁻¹ * r⁻¹ := by rw [har]
      _ = (r * r)⁻¹ := (mul_inv_rev r r).symm
      _ = r := by rw [hr2, inv_inv]
  have hc := cross_mul ρ (cross_conj ρ hrc.inv_left hac) hac
  simpa only [inv_inv, heq] using hc

/-- In a product of two cubic dihedral groups, quadratic cross-displacements
of the two generating involutions force the rotations to centralize each
other's displacements. No faithfulness or irreducibility is needed. -/
theorem dihedral_cubic_cross_displacements {r s a c : G}
    (ha : a * a = 1) (hc : c * c = 1) (hr : r ^ 3 = 1) (hs : s ^ 3 = 1)
    (har : a * r * a⁻¹ = r⁻¹) (hcs : c * s * c⁻¹ = s⁻¹)
    (hrc : Commute r c) (hrs : Commute r s)
    (hquad : ∀ v, ρ c (ρ a v - v) = ρ a v - v) :
    ∀ v, ρ s (ρ r v - v) = ρ r v - v := by
  have hcr := cross_cubic ρ ha hr har hrc hquad
  have hrc' := cross_symm ρ hrc hcr
  have hrs' := cross_cubic ρ hc hs hcs hrs.symm hrc'
  exact cross_symm ρ hrs.symm hrs'

end General

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem binary_neg (v : V) : -v = v := by
  calc -v = (-1 : ZMod 2) • v := (neg_one_smul _ v).symm
    _ = (1 : ZMod 2) • v := by congr 1
    _ = v := one_smul _ v

/-- The fixed-space assertion of GLS2 Lemma 25.12(iii), for two factors of
order six, expressed directly through generators and their relations. -/
theorem dihedral_cubic_fixed_iff {r s a c : G}
    (ha : a * a = 1) (hc : c * c = 1) (hr : r ^ 3 = 1) (hs : s ^ 3 = 1)
    (har : a * r * a⁻¹ = r⁻¹) (hcs : c * s * c⁻¹ = s⁻¹)
    (hrc : Commute r c) (hrs : Commute r s)
    (hquad : ∀ v, ρ c (ρ a v - v) = ρ a v - v) (v : V) :
    ρ (r * s) v = v ↔ ρ r v = v ∧ ρ s v = v := by
  constructor
  · intro hv
    have hd := dihedral_cubic_cross_displacements ρ ha hc hr hs har hcs hrc hrs hquad v
    have hsr : ρ s (ρ r v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← hrs.eq]
      exact hv
    rw [map_sub, hsr] at hd
    simp only [sub_eq_add_neg, binary_neg, add_comm v] at hd
    have heq : ρ s v = ρ r v := add_right_cancel hd
    have hrr : ρ r (ρ r v) = v := by
      rw [← heq, ← Module.End.mul_apply, ← map_mul]
      exact hv
    have hrv : ρ r v = v := by
      calc ρ r v = ρ r (ρ r (ρ r v)) := by rw [hrr]
        _ = ρ (r ^ 3) v := by simp [pow_succ, map_mul, Module.End.mul_apply]
        _ = v := by rw [hr, map_one]; rfl
    exact ⟨hrv, heq.trans hrv⟩
  · rintro ⟨hrv, hsv⟩
    simp [map_mul, Module.End.mul_apply, hrv, hsv]

end Representation.QuadraticFourGroup

end
