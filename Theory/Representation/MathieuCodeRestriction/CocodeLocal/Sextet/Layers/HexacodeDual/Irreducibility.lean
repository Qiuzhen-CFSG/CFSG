/-
The hexacode and affine sextet constructions used here are by Gerald Höhn and
ATLAS contributors, under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt. Their source modules record revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
-/
module

public import Theory.Representation.HexacodeAction
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeKernelTransitivity
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetSplitExtension
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Irreducibility of the binary hexacode and its affine dual

A small kernel-checked calculation on the 64 systematic codewords shows that
any nonzero invariant subspace contains a nonzero word vanishing at some
coordinate: either the original word does, or a displacement by one of the
five explicit coordinate lifts does. The existing local-kernel transitivity
then puts the entire zero-coordinate module in the subspace. Coordinate
permutations give every zero-coordinate module, and two of these span the
hexacode.

Surjectivity of the actual affine sextet quotient preserves irreducibility.
For the dual, the common kernel of an invariant space of linear forms is an
invariant subspace of the original module; finite-dimensional annihilator
duality gives the required zero-or-whole dichotomy.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400 (PDF p.411). These are the concrete irreducibility inputs for
the chief-factor identification. The middle-cocode pairing and its transport
are independent obligations. All code and action definitions are the actual
licensed ATLAS constructions, not abstract family labels.
-/

public section

open Atlas.Codes
namespace Representation.Hexacode

private theorem word_zero_or_displacement : ∀ x : Fin 3 → K, x ≠ 0 →
    (∃ i : HexIndex, systematicEncoder x i = 0) ∨
    ∃ k : Fin 5, Monomial.act (hexLiftRaw k) (systematicEncoder x) ≠ systematicEncoder x ∧
      ∃ i : HexIndex, Monomial.act (hexLiftRaw k) (systematicEncoder x) i = systematicEncoder x i := by
  decide +kernel

private theorem exists_nonzero_zero_coordinate (W : Subrepresentation action)
    (hW : W ≠ ⊥) : ∃ (i : HexIndex) (w : hexacode), w ∈ W ∧ w ≠ 0 ∧ w.val i = 0 := by
  have hn : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  obtain ⟨w, hw, hwn⟩ := W.toSubmodule.ne_bot_iff.mp hn
  have hx : hexProjection firstThree w ≠ 0 := by
    intro h
    apply hwn
    apply hexProjection_injective firstThree
    simpa using h
  have hc := word_zero_or_displacement (hexProjection firstThree w) hx
  rw [systematic_reconstruct] at hc
  rcases hc with ⟨i, hi⟩ | ⟨k, hk, i, hi⟩
  · exact ⟨i, w, hw, hwn, hi⟩
  · refine ⟨i, action (hexLift k) w - w,
      W.toSubmodule.sub_mem (W.apply_mem_toSubmodule _ hw) hw, ?_, ?_⟩
    · intro h
      exact hk (congrArg Subtype.val (sub_eq_zero.mp h))
    · change Monomial.act (hexLiftRaw k) w.val i - w.val i = 0
      exact sub_eq_zero.mpr hi

private theorem zero_coordinate_le (W : Subrepresentation action)
    (i : HexIndex) (w : hexacode) (hw : w ∈ W) (hwn : w ≠ 0) (hi : w.val i = 0) :
    hexZeroCoordinate i ≤ W.toSubmodule := by
  intro v hv
  by_cases hvn : v = 0
  · exact hvn ▸ W.toSubmodule.zero_mem
  let u : hexZeroCoordinate i := ⟨w, hi⟩
  let v' : hexZeroCoordinate i := ⟨v, hv⟩
  have hu : u ≠ 0 := fun h => hwn (congrArg Subtype.val h)
  have hv' : v' ≠ 0 := fun h => hvn (congrArg Subtype.val h)
  obtain ⟨g, hg⟩ := hexPointKernel_nonzero_transitive i u v' hu hv'
  have he : action g.val.val w = v := congrArg Subtype.val hg
  exact he ▸ W.apply_mem_toSubmodule g.val.val hw

private theorem all_zero_coordinates_le (W : Subrepresentation action)
    (i : HexIndex) (hi : hexZeroCoordinate i ≤ W.toSubmodule) (j : HexIndex) :
    hexZeroCoordinate j ≤ W.toSubmodule := by
  obtain ⟨g, hg⟩ := hexCoordinateHom_surjective (Equiv.swap i j)
  have hgi : g.val.perm i = j := by
    change hexCoordinateHom g i = j
    rw [hg, Equiv.swap_apply_left]
  intro v hv
  have hpre : action g⁻¹ v ∈ hexZeroCoordinate i := by
    change (g.val.localMap (g.val.perm i))⁻¹ (v.val (g.val.perm i)) = 0
    rw [hgi, show v.val j = 0 from hv, map_zero]
  have hm := W.apply_mem_toSubmodule g (hi hpre)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hm

/-- The actual binary hexacode representation is irreducible. -/
theorem action_isIrreducible : IsIrreducible action := by
  let : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (by rw [hexacode_finrank]; decide : 0 < Module.finrank Bit hexacode)
  refine ⟨fun W => ?_⟩
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  obtain ⟨i, w, hw, hwn, hi⟩ := exists_nonzero_zero_coordinate W hW
  have hAll := all_zero_coordinates_le W i (zero_coordinate_le W i w hw hwn hi)
  apply top_unique
  intro v _
  obtain ⟨u, hu0, hu1⟩ := hex_two_values (0,0) (0,1) (by decide) 0 (v.val (0,1))
  have hu : u ∈ W.toSubmodule := hAll (0,0) hu0
  have hvu : v - u ∈ W.toSubmodule := hAll (0,1) (by
    change v.val (0,1) - u.val (0,1) = 0
    rw [hu1, sub_self])
  change v ∈ W.toSubmodule
  simpa only [sub_add_cancel] using W.toSubmodule.add_mem hvu hu

/-- Pullback to the actual affine sextet stabilizer remains irreducible. -/
theorem sextet_action_isIrreducible : IsIrreducible (action.comp sextetQuotient) := by
  let : Nontrivial hexacode := Module.nontrivial_of_finrank_pos
    (by rw [hexacode_finrank]; decide : 0 < Module.finrank Bit hexacode)
  let : IsIrreducible action := action_isIrreducible
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation action :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule g v hv := by
        obtain ⟨s, rfl⟩ := sextetQuotient_surjective g
        exact W.apply_mem_toSubmodule s hv }
  rcases eq_bot_or_eq_top U with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation action => U.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun U : Subrepresentation action => U.toSubmodule) h

private theorem irreducible_dual {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

/-- The dual of the literal hexacode action pulled back to the affine stabilizer
is irreducible; its annihilators are invariant in the original representation. -/
theorem sextet_dual_isIrreducible : IsIrreducible (Representation.dual (action.comp sextetQuotient)) := by
  let : IsIrreducible (action.comp sextetQuotient) := sextet_action_isIrreducible
  exact irreducible_dual _

end Representation.Hexacode
