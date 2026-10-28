module

public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Omega
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Definite planes in the binary plus-four space

An anisotropic four-subgroup is one of the two original definite planes:
closure under addition forces its vectors into the same summand as any one
nonzero vector. Consequently an isometry interchanging the summands cannot
stabilize any definite plane. This retains the actual plane action required
for the distinction of the two Klein four-subgroups in 15.3.66(3).

Source: Aschbacher--Smith, combined manuscript (1 March 2004), printed
pp.1121--1122 and p.1152.
-/

@[expose] public section

open Subgroup Theory.AlgebraicGroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

def definitePlane (b : Bool) : Subgroup (Multiplicative Space) where
  carrier v := if b then v.toAdd.1 = 0 else v.toAdd.2 = 0
  one_mem' := by cases b <;> rfl
  mul_mem' := by
    intro u v hu hv
    cases b
    · change u.toAdd.2 + v.toAdd.2 = 0
      change u.toAdd.2 = 0 at hu
      change v.toAdd.2 = 0 at hv
      rw [hu,hv,add_zero]
    · change u.toAdd.1 + v.toAdd.1 = 0
      change u.toAdd.1 = 0 at hu
      change v.toAdd.1 = 0 at hv
      rw [hu,hv,add_zero]
  inv_mem' := by
    intro v hv
    cases b
    · change -v.toAdd.2 = 0
      change v.toAdd.2 = 0 at hv
      rw [hv,neg_zero]
    · change -v.toAdd.1 = 0
      change v.toAdd.1 = 0 at hv
      rw [hv,neg_zero]

theorem definitePlane_card (b : Bool) : Nat.card (definitePlane b) = 4 := by
  change Nat.card {x : Space // if b then x.1 = 0 else x.2 = 0} = 4
  rw [Nat.card_eq_fintype_card]
  cases b <;> decide +kernel

private theorem finite_definite : ∀ a : Space, a ≠ 0 → q a ≠ 0 →
    ∃ b : Bool, ∀ v : Space, (v ≠ 0 → q v ≠ 0) →
      (a+v ≠ 0 → q (a+v) ≠ 0) → (if b then v.1 = 0 else v.2 = 0) := by
  decide +kernel

/-- The only definite four-subgroups are the two original definite planes. -/
theorem definite_four_eq_plane (A : Subgroup (Multiplicative Space))
    (hcard : Nat.card A = 4) (ha : ∀ v ∈ A, v ≠ 1 → form v.toAdd ≠ 0) :
    ∃ b : Bool, A = definitePlane b := by
  have : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  obtain ⟨a,ha1⟩ := exists_ne (1 : A)
  have haz : a.val.toAdd ≠ 0 := fun h => ha1 (Subtype.ext h)
  have haq : q a.val.toAdd ≠ 0 := ha a.val a.property (fun h => ha1 (Subtype.ext h))
  obtain ⟨b,hb⟩ := finite_definite a.val.toAdd haz haq
  refine ⟨b, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro v hv
    apply hb v.toAdd
    · exact ha v hv
    · exact ha (a.val*v) (A.mul_mem a.property hv)
  · rw [definitePlane_card, hcard]

private theorem finite_moves_plane : ∀ k : Code, k.2.2 = true → ∀ b : Bool,
    ∃ v : Space, (if b then v.1 = 0 else v.2 = 0) ∧
      ¬ (if b then (eval k v).1 = 0 else (eval k v).2 = 0) := by decide +kernel

/-- An isometry interchanging the definite planes stabilizes neither of them. -/
theorem interchange_not_mem_plane (k : Code) (hk : k.2.2 = true) (b : Bool) :
    codeMap k ∉ lineStabilizer (definitePlane b) := by
  intro hg
  obtain ⟨v,hv,hmove⟩ := finite_moves_plane k hk b
  have h := (hg (Multiplicative.ofAdd v)).mpr hv
  change (if b then (candidate k v).1 = 0 else (candidate k v).2 = 0) at h
  rw [candidate_eval] at h
  exact hmove h

end OrthogonalFourBinary.SylowGeometry
