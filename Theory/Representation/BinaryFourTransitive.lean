module
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.Data.Fintype.Card
/-!
# Binary actions on a four-element vector space

An action with no nonzero globally fixed vector is transitive on the three
nonzero vectors. Otherwise a two-element orbit would leave the third vector
fixed. This supplies the order-four pair-section argument in DGS85 (11.3),
without choosing coordinates or assuming a faithful whole-group action.
-/

public noncomputable section
namespace Representation
open BinaryOffender
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

/-- A binary four-space with trivial global fixed space has one nonzero orbit. -/
theorem transitive_nonzero_of_card_four
    (ρ : Representation (ZMod 2) D W) (hcard : Nat.card W = 4)
    (hfixed : fixedSpace ρ ⊤ = ⊥) :
    ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ g : D, ρ g u = v := by
  classical
  let := Fintype.ofFinite W
  have hadd (x : W) : x + x = 0 := by
    rw [←two_nsmul x,←Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]
  intro u v hu hv
  by_contra! hno
  have huv : u ≠ v := by intro he; exact hno 1 ((show ρ 1 u = u from by rw [map_one]; rfl).trans he)
  have huv0 : u + v ≠ 0 := by
    intro he
    apply huv
    calc
      u = u + (v + v) := by rw [hadd,add_zero]
      _ = v := by rw [←add_assoc,he,zero_add]
  have hsumu : u+v ≠ u := by simpa using hv
  have hsumv : u+v ≠ v := by simpa using hu
  have henum (w : W) : w = 0 ∨ w = u ∨ w = v ∨ w = u+v := by
    have hc : ({0,u,v,u+v} : Finset W).card = 4 := by
      simp [huv,Ne.symm hu,Ne.symm hv,Ne.symm huv0,Ne.symm hsumu,Ne.symm hsumv]
    have he : ({0,u,v,u+v} : Finset W) = Finset.univ :=
      Finset.eq_univ_of_card _ (by simpa only [←Nat.card_eq_fintype_card,hcard] using hc)
    have hw : w ∈ ({0,u,v,u+v} : Finset W) := he.symm ▸ Finset.mem_univ w
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hw
  have hne (g : D) {x : W} (hx : x ≠ 0) : ρ g x ≠ 0 := by
    intro he
    have hh := congrArg (ρ g⁻¹) he
    exact hx (by simpa only [ρ.inv_self_apply,map_zero] using hh)
  obtain ⟨t,ht⟩ : ∃ t : D, ρ t u ≠ u := by
    by_contra! hh
    have hf : u ∈ fixedSpace ρ ⊤ := fun g => hh g
    exact hu (hfixed.le hf)
  have ht' : ρ t u = u+v := by
    rcases henum (ρ t u) with he | he | he | he
    · exact (hne t hu he).elim
    · exact (ht he).elim
    · exact (hno t he).elim
    · exact he
  have hf : v ∈ fixedSpace ρ ⊤ := by
    intro g
    change ρ g.val v = v
    rcases henum (ρ g.val v) with he | he | he | he
    · exact (hne g.val hv he).elim
    · apply False.elim
      apply hno g.val⁻¹
      rw [←he,ρ.inv_self_apply]
    · exact he
    · apply False.elim
      apply hno (g.val⁻¹*t)
      rw [map_mul,Module.End.mul_apply,ht',←he,ρ.inv_self_apply]
  exact hv (hfixed.le hf)
end Representation
