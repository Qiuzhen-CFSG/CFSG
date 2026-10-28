module
public import Theory.SpecificGroups.BinaryLinear.RadicalCut
public import Theory.Representation.BinaryNaturalDual.RadicalCore

/-!
# The natural-plus-dual fixed-space bound for a genuine radical

Every nontrivial binary linear radical contains a full block radical. Its
fixed vectors in natural plus dual lie in W times its annihilator, of dimension
the natural degree. This bound applies to the actual subgroup, without a
parabolic choice or a module classification assumption.
Source: Aschbacher--Smith C.4.8 and H.9, pp.154,389--392.
-/

public section
namespace BinaryNaturalDual
open BinaryLinear Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] [Nontrivial V]

/-- A nontrivial two-radical fixes at most half the natural-plus-dual space. -/
theorem finrank_fixedSpace_radical_le (P : Subgroup (BinaryLinear.GL V)) (hP : P.IsPRadical 2) :
    Module.finrank (ZMod 2) (Representation.BinaryOffender.fixedSpace naturalDualRepresentation P) ≤
      Module.finrank (ZMod 2) V := by
  obtain ⟨W,hW,hWt,hWP⟩ := BinaryLinear.exists_radical_cut P hP
  have hle : Representation.BinaryOffender.fixedSpace naturalDualRepresentation P ≤ W.prod W.dualAnnihilator := by
    rw [←fixedSpace_radical W hW hWt]
    intro v hv a
    exact hv ⟨a.val.val,hWP a.val.property⟩
  exact (Submodule.finrank_mono hle).trans_eq (finrank_prod_dualAnnihilator W)

end BinaryNaturalDual
