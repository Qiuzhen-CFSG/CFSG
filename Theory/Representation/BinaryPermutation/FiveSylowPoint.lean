module
public import Theory.Representation.BinaryAlternatingFiveBorel
public import Theory.Representation.BinaryPermutation.FiveSylowSingular
public import Theory.Representation.BinaryPermutation.FiveOrbits

/-!
# The singular point stabilizer of the binary A₅ module

A nonzero singular vector has a unique zero coordinate. Moving that coordinate
to the fifth point identifies its literal stabilizer with the standard A₄
Borel. This supplies the point quotient for the chief-factor comparison in
Aschbacher–Smith 13.4.10(1), printed p.908.
-/

public noncomputable section
open Subgroup BinaryPermutation
namespace BinaryPermutation.FiveSylowPoint
local instance : DecidablePred (· ∈ core (Fin 5)) := fun x =>
  inferInstanceAs (Decidable ((∑ i, x i) = 0))
local instance : Fintype (core (Fin 5)) := Subtype.fintype _

private theorem singular_point (v : core (Fin 5))
    (hv : v ≠ 0) (hs : FiveGeometry.form v = 0) :
    ∃ i : Fin 5, ∀ g : Equiv.Perm (Fin 5),
      coreRepresentation (Fin 5) g v = v ↔ g i = i := by
  have hh : ∀ v : core (Fin 5), v ≠ 0 → FiveGeometry.form v = 0 →
      ∃ i : Fin 5, ∀ g : Equiv.Perm (Fin 5),
        coreRepresentation (Fin 5) g v = v ↔ g i = i := by decide +kernel
  exact hh v hv hs

/-- The stabilizer of a nonzero singular vector in the five-point core is A4. -/
theorem stabilizer_equiv (v : core (Fin 5))
    (hv : v ≠ 0) (hs : FiveGeometry.form v = 0) :
    Nonempty (FiveOrbits.evenStabilizer v ≃* alternatingGroup (Fin 4)) := by
  obtain ⟨i,hi⟩ := singular_point v hv hs
  let s : Equiv.Perm (Fin 5) := Equiv.swap i 4
  let c : MulAut (alternatingGroup (Fin 5)) := MulAut.conjNormal s
  have hm : (FiveOrbits.evenStabilizer v).map c.toMonoidHom = AlternatingFiveBorel.B := by
    ext b
    constructor
    · rintro ⟨a,ha,rfl⟩
      have hai : a.val i = i := (hi a.val).mp ha
      change s (a.val (s⁻¹ 4)) = 4
      simp only [s,Equiv.swap_inv,Equiv.swap_apply_right,hai,Equiv.swap_apply_left]
    · intro hb
      refine ⟨c.symm b,?_,c.apply_symm_apply b⟩
      apply (hi (c.symm b).val).mpr
      change s⁻¹ (b.val (s i)) = i
      have hb4 : b.val 4 = 4 := hb
      simp only [s,Equiv.swap_inv,Equiv.swap_apply_left,hb4,Equiv.swap_apply_right]
  exact ⟨((FiveOrbits.evenStabilizer v).equivMapOfInjective c.toMonoidHom c.injective).trans
    ((MulEquiv.subgroupCongr hm).trans AlternatingFiveBorel.marking.symm)⟩

end BinaryPermutation.FiveSylowPoint
