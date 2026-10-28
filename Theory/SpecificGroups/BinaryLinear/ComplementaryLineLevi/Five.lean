module

public import Theory.SpecificGroups.BinaryLinear.ComplementaryLineLevi
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.Transport

/-!
# Maximality of the four-space parabolic in GL₅(2)

Transport a four-space to the last cut of a complete flag. The singleton-cut
stabilizer is maximal, and conjugation carries it to the literal stabilizer
of the original four-space. Together with the complementary-line results,
this identifies a genuine end-node Levi complement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.9(2)(iv), printed pp.94–95.
-/

public section

namespace BinaryLinear.ComplementaryLineLevi
open OuterCyclic FiveFlagGeometry FiveFlagGeometry.SylowOvergroups
open BinaryNaturalDual.FiveActors.Classification

/-- The stabilizer of a four-space in the binary five-space is maximal. -/
theorem fourSpace_parabolic_isCoatom (W : Submodule (ZMod 2) (Space 5))
    (hW : Module.finrank (ZMod 2) W = 4) : IsCoatom (parabolic W) := by
  let U := flagSpace standardBasis (3 : Fin 4)
  have hU : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W :=
    (finrank_flagSpace standardBasis (3 : Fin 4)).trans hW.symm
  obtain ⟨g, hg⟩ := exists_map_subspace_eq U W hU
  have hc := MaximalOvergroups.singleton_flag_isCoatom standardBasis (3 : Fin 4)
  rw [flagStabilizer_singleton] at hc
  have h : IsCoatom ((parabolic U).map (MulAut.conj g).toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr hc
  rwa [BinaryLinear.InvariantNodeActions.inner_map_parabolic, hg] at h

end BinaryLinear.ComplementaryLineLevi
