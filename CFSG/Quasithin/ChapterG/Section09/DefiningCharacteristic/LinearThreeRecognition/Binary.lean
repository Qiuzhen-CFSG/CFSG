module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Natural
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.Representation.Quotient

/-!
# Complete recognition over the smallest SL₃ field

The checked binary SL₃(2) catalogue has precisely the trivial, natural,
dual-natural and eight-dimensional adjoint modules. A nontrivial action
of degree at most six therefore is natural or dual natural. For a faithful
action of any nontrivial quotient, surjective inflation supplies the same
classification and proves that the quotient map has trivial kernel.

Source: Aschbacher--Smith, G.9.3(8), printed pp.354,356, with the concrete
H.6.1 catalogue. No higher-field classification is asserted here.
-/

public section

open Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- The smallest-field branch is exhaustive, with actual module equivalences. -/
theorem binary_small_module (ρ : Representation (ZMod 2) SL(3,ZMod 2) V)
    [IsIrreducible ρ] (hρ : ∃ g, ρ g ≠ 1)
    (hd : Module.finrank (ZMod 2) V ≤ 6) :
    Module.finrank (ZMod 2) V = 3 ∧
      (Nonempty (ρ.Equiv (naturalBinary (ZMod 2))) ∨
       Nonempty (ρ.Equiv (dualBinary (ZMod 2)))) := by
  have hmove : ∃ g v, ρ g v ≠ v := by
    by_contra! h
    obtain ⟨g, hg⟩ := hρ
    exact hg (LinearMap.ext (h g))
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial ρ hmove with
    h | h | h
  · obtain ⟨e⟩ := h
    refine ⟨?_, Or.inl ⟨e⟩⟩
    simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using e.toLinearEquiv.finrank_eq
  · obtain ⟨e⟩ := h
    let f := e.trans (dualBinaryEquiv (ZMod 2)).symm
    refine ⟨?_, Or.inr ⟨f⟩⟩
    exact f.toLinearEquiv.finrank_eq.trans (naturalBinary_finrank (ZMod 2) (n := 1) (by simp))
  · obtain ⟨e⟩ := h
    have hh := e.toLinearEquiv.finrank_eq.trans BinaryLinearThree.finrank_steinberg
    omega

/-- A faithful small irreducible of a nontrivial quotient of SL₃(2)
identifies both its component and its module. -/
theorem binary_small_quotient {L : Type*} [Group L] [Nontrivial L]
    (π : SL(3,ZMod 2) →* L) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) L V) [IsIrreducible ρ]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 6) :
    π.ker = ⊥ ∧ Nonempty (L ≃* SL(3,ZMod 2)) ∧
      Module.finrank (ZMod 2) V = 3 ∧
      (Nonempty (Representation.Equiv (ρ.comp π) (naturalBinary (ZMod 2))) ∨
       Nonempty (Representation.Equiv (ρ.comp π) (dualBinary (ZMod 2)))) := by
  let : IsIrreducible (ρ.comp π) := (irreducible_comp_surjective_iff π hπ ρ).mpr inferInstance
  have hnon : ∃ g, (ρ.comp π) g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    obtain ⟨g, rfl⟩ := hπ x
    refine ⟨g, fun hg => hx (hρ ?_)⟩
    exact hg.trans ρ.map_one.symm
  obtain ⟨hdim, hnat⟩ := binary_small_module (ρ.comp π) hnon hd
  obtain ⟨hk, he, _⟩ := natural_cover_recognition (ZMod 2) π hπ ρ
    (n := 1) (by simp) hnat
  exact ⟨hk, he, hdim, hnat⟩

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
