module

public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerDerived
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField
public import Mathlib.GroupTheory.IsPerfect

/-!
# Solvable Borels and the nonbinary derived symplectic carrier

The two determinant characters put the Borel commutator in its unipotent
two-subgroup. Finite two-groups are nilpotent, so the Borel and every Sylow
two-normalizer are solvable. Over a characteristic-two field of order greater
than two, root generation and torus commutators make the full matrix group
perfect. Its derived carrier is therefore identified with it by inclusion.

The imported root-generation theorem uses exactly
`Matrix.symplecticGroup (Fin 2) F`; no change of matrix model is involved.
This modern module supplies the characteristic-two specialization of the
argument also developed in the legacy ATLAS `Symplectic/PerfectLarge` port.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, B.4.2(3), printed p.86; B.5.5(1)(iv), pp.104–105;
and the Borel used in the proof of 15.3.49(k), p.1144.
-/

public section

open Subgroup

private theorem solvable_of_derived_le {G : Type*} [Group G]
    (H K : Subgroup G) [Group.IsSolvable K] (hc : ⁅H, H⁆ ≤ K) :
    Group.IsSolvable H := by
  let f : commutator H →* K :=
    (H.subtype.comp (commutator H).subtype).codRestrict K (fun x => hc (by
      rw [← map_subtype_commutator]
      exact ⟨x.val, x.property, rfl⟩))
  let _ : Group.IsSolvable (commutator H) :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun x : K => (x : G)) h)))
  exact Group.isSolvable_of_ker_le_range (commutator H).subtype Abelianization.of (by
    rw [Abelianization.ker_of, range_subtype])

namespace Theory.SpecificGroups.SymplecticFour

variable {F : Type*} [Field F] [Finite F]

/-- The concrete flag Borel is solvable over a field of two-power order. -/
theorem isSolvable_borel {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Group.IsSolvable (borel (F := F)) := by
  let _ := (isPGroup_unipotent hF).isNilpotent
  exact solvable_of_derived_le borel unipotent commutator_borel_le_unipotent

/-- Every Sylow two-normalizer in the full symplectic matrix group is solvable. -/
theorem isSolvable_sylow_normalizer {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (P : Sylow 2 (Sp F)) :
    Group.IsSolvable (normalizer (P : Set (Sp F))) := by
  let _ := P.isPGroup'.isNilpotent
  exact solvable_of_derived_le _ (P : Subgroup (Sp F))
    (commutator_sylow_normalizer_le hF hn P)

/-- Root generation proves perfectness of the native nonbinary matrix carrier. -/
theorem perfect_of_card_gt_two [CharP F 2] (hF : 2 < Nat.card F) :
    Group.IsPerfect (Sp F) :=
  ⟨Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hF⟩

/-- For nonexceptional fields the inclusion of the derived subgroup is an isomorphism. -/
noncomputable def derivedEquivFull_of_card_gt_two [CharP F 2] (hq : 2 < Nat.card F) :
    commutator (Sp F) ≃* Sp F := by
  let _ := perfect_of_card_gt_two hq
  exact (MulEquiv.subgroupCongr (Group.IsPerfect.commutator_eq_top (G := Sp F))).trans
    Subgroup.topEquiv

@[simp] theorem derivedEquivFull_of_card_gt_two_apply [CharP F 2]
    (hq : 2 < Nat.card F) (g : commutator (Sp F)) :
    derivedEquivFull_of_card_gt_two hq g = (g : Sp F) := by rfl

end Theory.SpecificGroups.SymplecticFour
