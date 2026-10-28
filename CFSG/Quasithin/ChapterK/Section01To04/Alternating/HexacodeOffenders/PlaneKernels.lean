module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.HexacodeOffenders.Coordinates

/-!
# Field subspaces have even pointwise fixers

An odd hexacode operator is semilinear for the nontrivial field
automorphism. If it fixes both a vector and its primitive scalar multiple,
that vector is zero. Thus the pointwise fixer of any nonzero F₄ subspace
is contained in the even cover. In particular the literal plane kernel in
the triple-S₆ action is the image of the corresponding kernel in triple-A₆.

This is the kernel comparison needed in K.1.3, Aschbacher–Smith, combined
manuscript, printed p.453. It does not yet exclude every best offender
containing an odd involution, since its fixed space need not be an F₄ subspace.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes

namespace CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
open ChapterB.QuasisimpleSource

/-- An odd operator cannot fix a nonzero vector together with its scalar multiple. -/
theorem eq_zero_of_odd_fixes_scalar (g : HexAutomorphisms) (hg : hexSign g = -1)
    (v : hexacode) (hv : Hexacode.action g v = v)
    (hs : Hexacode.action g (Hexacode.omega • v) = Hexacode.omega • v) : v = 0 := by
  have h := Hexacode.action_odd_smul g hg Hexacode.omega v
  rw [hs, hv] at h
  have hz : (Hexacode.omega - SL2FourNatural.fieldFrobenius Hexacode.omega) • v = 0 := by
    rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left
    (sub_ne_zero.mpr (by decide : Hexacode.omega ≠
      SL2FourNatural.fieldFrobenius Hexacode.omega))

/-- Any nonzero field subspace has its full pointwise kernel in the even cover. -/
theorem planeKernel_le_even
    (P : Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier))
    (hP : P ≠ ⊥) :
    subspaceKernel Hexacode.action
      ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap) ⊤ ≤ hexSign.ker := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  let v := modelCoordinates.symm w
  have hvP : modelCoordinates v ∈ P := by rwa [modelCoordinates.apply_symm_apply]
  intro g hg
  rcases Int.units_eq_one_or (hexSign g) with he | ho
  · exact he
  · exfalso
    have hv : Hexacode.action g v = v := hg.2 v hvP
    have hs : Hexacode.action g (Hexacode.omega • v) = Hexacode.omega • v := by
      apply hg.2
      change modelCoordinates (Hexacode.omega • v) ∈ P
      rw [modelCoordinates_smul]
      exact P.smul_mem _ hvP
    have hz := eq_zero_of_odd_fixes_scalar g ho v hv hs
    apply hw0
    calc
      w = modelCoordinates v := (modelCoordinates.apply_symm_apply w).symm
      _ = 0 := by rw [hz, map_zero]

/-- The plane kernel in the full group is precisely the embedded even kernel. -/
theorem planeKernel_even_map
    (P : Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier))
    (hP : Module.finrank BinaryField.four.Carrier P = 2) :
    (subspaceKernel Hexacode.evenAction
      ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap) ⊤).map
      hexSign.ker.subtype = subspaceKernel Hexacode.action
        ((P.restrictScalars (ZMod 2)).comap modelCoordinates.toLinearMap) ⊤ := by
  have hn : P ≠ ⊥ := by
    intro hz
    rw [hz] at hP
    simp at hP
  ext x
  constructor
  · rintro ⟨g, ⟨_, hg⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, hg⟩
  · intro hx
    exact ⟨⟨x, planeKernel_le_even P hn hx⟩, ⟨Subgroup.mem_top _, hx.2⟩, rfl⟩

end CFSG.Quasithin.ChapterK.Alternating.HexacodeOffenders
