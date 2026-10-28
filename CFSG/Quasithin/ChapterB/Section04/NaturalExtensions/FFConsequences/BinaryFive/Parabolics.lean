module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.BinaryFive.Bounds
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalOvergroups
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality

/-!
# Genuine maximal parabolics for the high-rank B.4.9 alternatives

An arbitrary proper subspace is carried to a marked flag cut by a linear
isomorphism. Maximality of the singleton-cut stabilizer therefore applies
to its actual stabilizer. The block radical is the embedded intrinsic
two-core. This completes the parabolic placement for ranks five and six,
including both interior nodes, without assuming the extension splits.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(2)(iv),
printed p.95.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
open QuasisimpleSource BinaryLinear BinaryLinear.OuterCyclic
open BinaryLinear.FiveFlagGeometry BinaryLinear.FiveFlagGeometry.SylowOvergroups
open BinaryNaturalDual.FiveActors.Classification

private theorem parabolic_isCoatom (W : Submodule (ZMod 2) (Space 5))
    (hpos : 0 < Module.finrank (ZMod 2) W) (hlt : Module.finrank (ZMod 2) W < 5) :
    IsCoatom (parabolic W) := by
  let i : Fin 4 := ⟨Module.finrank (ZMod 2) W - 1, by omega⟩
  let U := flagSpace standardBasis i
  have hU : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) W := by
    rw [finrank_flagSpace]
    dsimp [i]
    omega
  obtain ⟨g, hg⟩ := exists_map_subspace_eq U W hU
  have hc := MaximalOvergroups.singleton_flag_isCoatom standardBasis i
  rw [flagStabilizer_singleton] at hc
  have h : IsCoatom ((parabolic U).map (MulAut.conj g).toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup _).mpr hc
  rwa [BinaryLinear.InvariantNodeActions.inner_map_parabolic, hg] at h

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {ρ : Representation (ZMod 2) G V}
  (d : DoubleNatural F 5 ρ) (hF : F.degree = 1)

/-- Placement in the genuine unipotent radical of a maximal interior-node
parabolic. Its two-core is computed inside the parabolic before embedding. -/
theorem interior_parabolic_placement {A : Subgroup G} (hA : IsElementaryTwo A)
    (hr : 5 ≤ rank A) :
    ∃ W : Submodule (ZMod 2) (Space 5),
      (Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3) ∧
      IsCoatom (parabolic W) ∧
      A.map (groupEquiv d hF).toMonoidHom ≤ radical W ∧
      radical W = (pCore 2 (parabolic W)).map (parabolic W).subtype := by
  obtain ⟨W, hW, hA⟩ := interior_placement d hF hA hr
  exact ⟨W, hW, parabolic_isCoatom W (by omega) (by omega), hA,
    (SmallParabolicLevi.map_twoCore_eq_radical W).symm⟩
end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive
