module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.NormNum
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# The `A₆`/`S₆` rank-two quadrangle

This file records the concrete small geometry used in I.5.4--I.5.9.  The
fifteen duads and fifteen synthemes on six letters are listed explicitly.
Finite incidence assertions are checked by kernel reduction. The standard
subgroups fix the incident duad `{01}` and syntheme `{01,23,45}`; their
intersections with `A₆` give the alternating-group models.

The two parabolics have orders 48 in S₆ and 24 in A₆. Their intersections
have orders 16 and 8, respectively, and are Sylow two-subgroups. Every proper
overgroup of the chosen Sylow subgroup lies in one of these two parabolics;
thus the parabolics are distinct, maximal, and exhaustive.

For the overgroup assertion, a kernel-checked table writes every even
permutation as a product of two Borel elements and one of nine representatives.
Short word certificates recover a fixed generator outside each parabolic
from any representative outside it. Together with the Borel these generators
produce A₆. Multiplication by the odd Borel element `(01)` transfers the
result to S₆. Conjugation then treats arbitrary Sylow two-subgroups.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, I.5,
printed pp. 419--422.
-/

@[expose] public section

namespace Theory.SpecificGroups.SymmetricSix

open Finset

abbrev Letter := Fin 6
abbrev Duad := Fin 15
abbrev Syntheme := Fin 15

def pair (i j : Letter) : Finset Letter := {i, j}

def duadTable : List (Finset Letter) :=
  [pair 0 1, pair 0 2, pair 0 3, pair 0 4, pair 0 5,
   pair 1 2, pair 1 3, pair 1 4, pair 1 5,
   pair 2 3, pair 2 4, pair 2 5,
   pair 3 4, pair 3 5, pair 4 5]

def duadSet (d : Duad) : Finset Letter :=
  duadTable.get ⟨d.1, by simp [duadTable]⟩

def synthemeTable : List (Finset Duad) :=
  [{0, 9, 14}, {0, 10, 13}, {0, 11, 12},
   {1, 6, 14}, {1, 7, 13}, {1, 8, 12},
   {2, 5, 14}, {2, 7, 11}, {2, 8, 10},
   {3, 5, 13}, {3, 6, 11}, {3, 8, 9},
   {4, 5, 12}, {4, 6, 10}, {4, 7, 9}]

def synthemeDuads (s : Syntheme) : Finset Duad :=
  synthemeTable.get ⟨s.1, by simp [synthemeTable]⟩

def incident (d : Duad) (s : Syntheme) : Prop := d ∈ synthemeDuads s

def duadCollinear (d e : Duad) : Prop :=
  d ≠ e ∧ (duadSet d ∩ duadSet e).card = 0

def synthemeCollinear (s t : Syntheme) : Prop :=
  s ≠ t ∧ (synthemeDuads s ∩ synthemeDuads t).card = 1

instance duadCollinear_decidable (d e : Duad) : Decidable (duadCollinear d e) := by
  unfold duadCollinear
  infer_instance

instance synthemeCollinear_decidable (s t : Syntheme) : Decidable (synthemeCollinear s t) := by
  unfold synthemeCollinear
  infer_instance

instance incident_decidable (d : Duad) (s : Syntheme) : Decidable (incident d s) := by
  unfold incident
  infer_instance

def duadCommon (d e : Duad) : Finset Duad :=
  Finset.univ.filter (fun f => decide (duadCollinear d f ∧ duadCollinear e f))

def synthemeCommon (s t : Syntheme) : Finset Syntheme :=
  Finset.univ.filter (fun u => decide (synthemeCollinear s u ∧ synthemeCollinear t u))

theorem duad_card : Fintype.card Duad = 15 := by decide

theorem syntheme_card : Fintype.card Syntheme = 15 := by decide

theorem duad_is_duad (d : Duad) : (duadSet d).card = 2 := by
  fin_cases d <;> decide

theorem syntheme_is_partition (s : Syntheme) :
    (synthemeDuads s).card = 3 ∧
      (synthemeDuads s).biUnion duadSet = Finset.univ := by
  fin_cases s <;> decide

theorem duad_incidence_three (d : Duad) :
    (Finset.univ.filter (fun s : Syntheme => incident d s)).card = 3 := by
  fin_cases d <;> decide

theorem syntheme_incidence_three (s : Syntheme) :
    (Finset.univ.filter (fun d : Duad => incident d s)).card = 3 := by
  fin_cases s <;> decide

theorem duad_collinear_six (d : Duad) :
    (Finset.univ.filter (duadCollinear d)).card = 6 := by
  fin_cases d <;> decide

theorem syntheme_collinear_six (s : Syntheme) :
    (Finset.univ.filter (synthemeCollinear s)).card = 6 := by
  fin_cases s <;> decide

theorem duad_noncollinear_eight (d : Duad) :
    (Finset.univ.filter (fun e => e ≠ d ∧ ¬duadCollinear d e)).card = 8 := by
  fin_cases d <;> decide

theorem syntheme_noncollinear_eight (s : Syntheme) :
    (Finset.univ.filter (fun t => t ≠ s ∧ ¬synthemeCollinear s t)).card = 8 := by
  fin_cases s <;> decide

theorem duad_common_three {d e : Duad} (h : d ≠ e) (hn : ¬duadCollinear d e) :
    (duadCommon d e).card = 3 := by
  decide +revert

theorem syntheme_common_three {s t : Syntheme} (h : s ≠ t)
    (hn : ¬synthemeCollinear s t) : (synthemeCommon s t).card = 3 := by
  decide +revert

abbrev NaturalModule := (Fin 2 ⊕ Fin 2) → ZMod 2
abbrev BinaryPoint := {v : NaturalModule // v ≠ 0}

instance binaryPointFintype : Fintype BinaryPoint :=
  Fintype.subtype (Finset.univ.filter (fun v : NaturalModule => v ≠ 0)) (by simp)

def vec (a b c d : ZMod 2) : NaturalModule :=
  fun i => match i with
    | Sum.inl j => if j = 0 then a else b
    | Sum.inr j => if j = 0 then c else d

def polarTable : List BinaryPoint :=
  [⟨vec 0 0 0 1, by decide⟩, ⟨vec 0 1 0 0, by decide⟩,
   ⟨vec 0 1 1 1, by decide⟩, ⟨vec 1 1 0 1, by decide⟩,
   ⟨vec 1 1 1 1, by decide⟩, ⟨vec 0 1 0 1, by decide⟩,
   ⟨vec 0 1 1 0, by decide⟩, ⟨vec 1 1 0 0, by decide⟩,
   ⟨vec 1 1 1 0, by decide⟩, ⟨vec 0 0 1 1, by decide⟩,
   ⟨vec 1 0 0 1, by decide⟩, ⟨vec 1 0 1 1, by decide⟩,
   ⟨vec 1 0 1 0, by decide⟩, ⟨vec 1 0 0 0, by decide⟩,
   ⟨vec 0 0 1 0, by decide⟩]

def polarVector (d : Duad) : BinaryPoint :=
  polarTable.get ⟨d.1, by simp [polarTable]⟩

theorem binary_point_card : Fintype.card BinaryPoint = 15 := by decide

theorem natural_symplectic_group_finite :
    Finite (Matrix.symplecticGroup (Fin 2) (ZMod 2)) := by infer_instance

theorem natural_polar_space_card :
    Nat.card BinaryPoint = 15 := by
  rw [Nat.card_eq_fintype_card]
  exact binary_point_card

abbrev S6 := Equiv.Perm Letter
abbrev A6 := alternatingGroup Letter

instance permFinsetAction : MulAction S6 (Finset Letter) where
  smul g s := s.image g
  one_smul s := by
    change s.image (1 : S6) = s
    simp
  mul_smul g h s := by
    change s.image (g * h) = (s.image h).image g
    simp [Finset.image_image]

instance permPartitionAction : MulAction S6 (Finset (Finset Letter)) where
  smul g s := s.image (fun t => t.image g)
  one_smul s := by
    change s.image (fun t => t.image (1 : S6)) = s
    simp
  mul_smul g h s := by
    change s.image (fun t => t.image (g * h)) =
      (s.image (fun t => t.image h)).image (fun t => t.image g)
    apply Finset.ext
    intro x
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.image h, ⟨a, ha, rfl⟩, ?_⟩
      rw [Finset.image_image]
      rfl
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      rw [Finset.image_image]
      rfl

/-- The standard point parabolic, fixing the duad `{0,1}`. -/
def duadStabilizer : Subgroup S6 := MulAction.stabilizer S6 (pair 0 1)

/-- The standard syntheme `{01,23,45}`. -/
def baseSyntheme : Finset (Finset Letter) := {pair 0 1, pair 2 3, pair 4 5}

/-- The standard line parabolic, fixing the partition `{01,23,45}`. -/
def synthemeStabilizer : Subgroup S6 := MulAction.stabilizer S6 baseSyntheme

/-- The intersection of the two incident standard parabolics. -/
def borel : Subgroup S6 := duadStabilizer ⊓ synthemeStabilizer

def a6DuadStabilizer : Subgroup A6 := duadStabilizer.comap A6.subtype
def a6SynthemeStabilizer : Subgroup A6 := synthemeStabilizer.comap A6.subtype
def a6Borel : Subgroup A6 := borel.comap A6.subtype

theorem s6_order : Nat.card S6 = 720 := by
  norm_num [S6, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem a6_order : Nat.card A6 = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

theorem a6_center_eq_bot : Subgroup.center A6 = ⊥ := by
  exact alternatingGroup.center_eq_bot (by norm_num)

instance (g : S6) : Decidable (g ∈ duadStabilizer) := by
  change Decidable ((pair 0 1).image g = pair 0 1)
  infer_instance
instance (g : S6) : Decidable (g ∈ synthemeStabilizer) := by
  change Decidable (baseSyntheme.image (fun t => t.image g) = baseSyntheme)
  infer_instance
instance (g : S6) : Decidable (g ∈ borel) := inferInstanceAs (Decidable (g ∈ duadStabilizer ∧ g ∈ synthemeStabilizer))
instance (g : A6) : Decidable (g ∈ a6DuadStabilizer) := inferInstanceAs (Decidable (g.val ∈ duadStabilizer))
instance (g : A6) : Decidable (g ∈ a6SynthemeStabilizer) := inferInstanceAs (Decidable (g.val ∈ synthemeStabilizer))
instance (g : A6) : Decidable (g ∈ a6Borel) := inferInstanceAs (Decidable (g.val ∈ borel))
instance (g : S6) : Decidable (g ∈ alternatingGroup Letter) :=
  inferInstanceAs (Decidable (Equiv.Perm.sign g = 1))

section Orders
-- The direct permutation enumerator avoids transporting through arbitrary
-- equivalences with `Fin (Fintype.card Letter)` during kernel computation.
local instance : Fintype S6 := fintypePerm
local instance : Fintype A6 := Subtype.fintype _

set_option maxRecDepth 100000 in
theorem duadStabilizer_order : Nat.card duadStabilizer = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
theorem synthemeStabilizer_order : Nat.card synthemeStabilizer = 48 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
theorem borel_order : Nat.card borel = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
theorem a6DuadStabilizer_order : Nat.card a6DuadStabilizer = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
theorem a6SynthemeStabilizer_order : Nat.card a6SynthemeStabilizer = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
set_option maxRecDepth 100000 in
theorem a6Borel_order : Nat.card a6Borel = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
end Orders

theorem duadStabilizer_index : duadStabilizer.index = 15 := by
  have h := duadStabilizer.card_mul_index
  rw [duadStabilizer_order, s6_order] at h
  omega

theorem synthemeStabilizer_index : synthemeStabilizer.index = 15 := by
  have h := synthemeStabilizer.card_mul_index
  rw [synthemeStabilizer_order, s6_order] at h
  omega

theorem borel_index : borel.index = 45 := by
  have h := borel.card_mul_index
  rw [borel_order, s6_order] at h
  omega

theorem a6DuadStabilizer_index : a6DuadStabilizer.index = 15 := by
  have h := a6DuadStabilizer.card_mul_index
  rw [a6DuadStabilizer_order, a6_order] at h
  omega

theorem a6SynthemeStabilizer_index : a6SynthemeStabilizer.index = 15 := by
  have h := a6SynthemeStabilizer.card_mul_index
  rw [a6SynthemeStabilizer_order, a6_order] at h
  omega

theorem a6Borel_index : a6Borel.index = 45 := by
  have h := a6Borel.card_mul_index
  rw [a6Borel_order, a6_order] at h
  omega

theorem borel_le_duadStabilizer : borel ≤ duadStabilizer := inf_le_left
theorem borel_le_synthemeStabilizer : borel ≤ synthemeStabilizer := inf_le_right
theorem a6Borel_le_duadStabilizer : a6Borel ≤ a6DuadStabilizer :=
  Subgroup.comap_mono inf_le_left
theorem a6Borel_le_synthemeStabilizer : a6Borel ≤ a6SynthemeStabilizer :=
  Subgroup.comap_mono inf_le_right

theorem a6_parabolics_inf : a6DuadStabilizer ⊓ a6SynthemeStabilizer = a6Borel := rfl

/-- The stabilizer of the standard incident flag is a Sylow two-subgroup of S₆. -/
noncomputable def borelSylow : Sylow 2 S6 :=
  (IsPGroup.of_card (show Nat.card borel = 2 ^ 4 by rw [borel_order]; decide)).toSylow
    (by rw [borel_index]; decide)

@[simp] theorem borelSylow_coe : (borelSylow : Subgroup S6) = borel := rfl

/-- The alternating flag stabilizer is a Sylow two-subgroup of A₆. -/
noncomputable def a6BorelSylow : Sylow 2 A6 :=
  (IsPGroup.of_card (show Nat.card a6Borel = 2 ^ 3 by rw [a6Borel_order]; decide)).toSylow
    (by rw [a6Borel_index]; decide)

@[simp] theorem a6BorelSylow_coe : (a6BorelSylow : Subgroup A6) = a6Borel := rfl

theorem parabolics_inf : duadStabilizer ⊓ synthemeStabilizer = borel := rfl

theorem borel_relIndex_duad : borel.relIndex duadStabilizer = 3 := by
  have h := Subgroup.relIndex_mul_index borel_le_duadStabilizer
  rw [duadStabilizer_index, borel_index] at h
  omega

theorem borel_relIndex_syntheme : borel.relIndex synthemeStabilizer = 3 := by
  have h := Subgroup.relIndex_mul_index borel_le_synthemeStabilizer
  rw [synthemeStabilizer_index, borel_index] at h
  omega

theorem a6Borel_relIndex_duad : a6Borel.relIndex a6DuadStabilizer = 3 := by
  have h := Subgroup.relIndex_mul_index a6Borel_le_duadStabilizer
  rw [a6DuadStabilizer_index, a6Borel_index] at h
  omega

theorem a6Borel_relIndex_syntheme : a6Borel.relIndex a6SynthemeStabilizer = 3 := by
  have h := Subgroup.relIndex_mul_index a6Borel_le_synthemeStabilizer
  rw [a6SynthemeStabilizer_index, a6Borel_index] at h
  omega

namespace Certificate
private def upper : Fin 8 → A6 :=
  ![⟨1, by decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 2 5 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩]
private def rep : Fin 9 → A6 :=
  ![⟨1, by decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 4, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩]
private def a : A6 := ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by decide⟩
private def b : A6 := ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩
private def allEven : List S6 :=
  (permsOfList [0, 1, 2, 3, 4, 5]).filter (fun g => Equiv.Perm.sign g = 1)
private def factors : List (Fin 8 × Fin 9 × Fin 8) :=
  [⟨7, 0, 6⟩, ⟨3, 1, 2⟩, ⟨7, 1, 5⟩, ⟨7, 0, 7⟩, ⟨7, 1, 6⟩, ⟨3, 1, 1⟩, ⟨7, 1, 7⟩, ⟨3, 1, 3⟩, ⟨7, 0, 5⟩, ⟨3, 1, 0⟩, ⟨7, 0, 4⟩, ⟨7, 1, 4⟩,
   ⟨0, 2, 0⟩, ⟨0, 3, 0⟩, ⟨0, 4, 0⟩, ⟨0, 2, 1⟩, ⟨0, 4, 3⟩, ⟨0, 3, 2⟩, ⟨0, 4, 2⟩, ⟨0, 3, 1⟩, ⟨0, 2, 3⟩, ⟨0, 3, 3⟩, ⟨0, 2, 2⟩, ⟨0, 4, 1⟩,
   ⟨1, 2, 1⟩, ⟨1, 3, 2⟩, ⟨1, 4, 3⟩, ⟨1, 2, 0⟩, ⟨1, 4, 0⟩, ⟨1, 3, 0⟩, ⟨1, 4, 1⟩, ⟨1, 3, 3⟩, ⟨1, 2, 2⟩, ⟨1, 3, 1⟩, ⟨1, 2, 3⟩, ⟨1, 4, 2⟩,
   ⟨2, 2, 3⟩, ⟨2, 3, 1⟩, ⟨2, 4, 2⟩, ⟨2, 2, 2⟩, ⟨2, 4, 1⟩, ⟨2, 3, 3⟩, ⟨2, 4, 0⟩, ⟨2, 3, 0⟩, ⟨2, 2, 0⟩, ⟨2, 3, 2⟩, ⟨2, 2, 1⟩, ⟨2, 4, 3⟩,
   ⟨3, 2, 2⟩, ⟨3, 3, 3⟩, ⟨3, 4, 1⟩, ⟨3, 2, 3⟩, ⟨3, 4, 2⟩, ⟨3, 3, 1⟩, ⟨3, 4, 3⟩, ⟨3, 3, 2⟩, ⟨3, 2, 1⟩, ⟨3, 3, 0⟩, ⟨3, 2, 0⟩, ⟨3, 4, 0⟩,
   ⟨7, 0, 2⟩, ⟨3, 1, 6⟩, ⟨7, 1, 1⟩, ⟨7, 0, 3⟩, ⟨7, 1, 2⟩, ⟨3, 1, 5⟩, ⟨7, 1, 3⟩, ⟨3, 1, 7⟩, ⟨7, 0, 1⟩, ⟨3, 1, 4⟩, ⟨7, 0, 0⟩, ⟨7, 1, 0⟩,
   ⟨4, 2, 0⟩, ⟨4, 4, 0⟩, ⟨4, 3, 0⟩, ⟨4, 2, 1⟩, ⟨4, 3, 2⟩, ⟨4, 4, 3⟩, ⟨4, 3, 3⟩, ⟨4, 4, 1⟩, ⟨4, 2, 2⟩, ⟨4, 4, 2⟩, ⟨4, 2, 3⟩, ⟨4, 3, 1⟩,
   ⟨5, 2, 1⟩, ⟨5, 4, 3⟩, ⟨5, 3, 2⟩, ⟨5, 2, 0⟩, ⟨5, 3, 0⟩, ⟨5, 4, 0⟩, ⟨5, 3, 1⟩, ⟨5, 4, 2⟩, ⟨5, 2, 3⟩, ⟨5, 4, 1⟩, ⟨5, 2, 2⟩, ⟨5, 3, 3⟩,
   ⟨6, 2, 2⟩, ⟨6, 4, 1⟩, ⟨6, 3, 3⟩, ⟨6, 2, 3⟩, ⟨6, 3, 1⟩, ⟨6, 4, 2⟩, ⟨6, 3, 0⟩, ⟨6, 4, 0⟩, ⟨6, 2, 0⟩, ⟨6, 4, 3⟩, ⟨6, 2, 1⟩, ⟨6, 3, 2⟩,
   ⟨7, 2, 3⟩, ⟨7, 4, 2⟩, ⟨7, 3, 1⟩, ⟨7, 2, 2⟩, ⟨7, 3, 3⟩, ⟨7, 4, 1⟩, ⟨7, 3, 2⟩, ⟨7, 4, 3⟩, ⟨7, 2, 1⟩, ⟨7, 4, 0⟩, ⟨7, 2, 0⟩, ⟨7, 3, 0⟩,
   ⟨4, 2, 4⟩, ⟨4, 4, 4⟩, ⟨4, 3, 4⟩, ⟨4, 2, 5⟩, ⟨4, 3, 6⟩, ⟨4, 4, 7⟩, ⟨4, 3, 7⟩, ⟨4, 4, 5⟩, ⟨4, 2, 6⟩, ⟨4, 4, 6⟩, ⟨4, 2, 7⟩, ⟨4, 3, 5⟩,
   ⟨0, 2, 4⟩, ⟨0, 3, 4⟩, ⟨0, 4, 4⟩, ⟨0, 2, 5⟩, ⟨0, 4, 7⟩, ⟨0, 3, 6⟩, ⟨0, 4, 6⟩, ⟨0, 3, 5⟩, ⟨0, 2, 7⟩, ⟨0, 3, 7⟩, ⟨0, 2, 6⟩, ⟨0, 4, 5⟩,
   ⟨5, 5, 5⟩, ⟨4, 6, 3⟩, ⟨5, 6, 7⟩, ⟨5, 5, 4⟩, ⟨5, 6, 4⟩, ⟨4, 6, 0⟩, ⟨5, 6, 5⟩, ⟨4, 6, 2⟩, ⟨5, 5, 6⟩, ⟨4, 6, 1⟩, ⟨5, 5, 7⟩, ⟨5, 6, 6⟩,
   ⟨0, 7, 0⟩, ⟨2, 8, 4⟩, ⟨2, 7, 4⟩, ⟨0, 7, 1⟩, ⟨2, 7, 7⟩, ⟨2, 8, 6⟩, ⟨2, 7, 6⟩, ⟨2, 8, 5⟩, ⟨0, 7, 2⟩, ⟨2, 8, 7⟩, ⟨0, 7, 3⟩, ⟨2, 7, 5⟩,
   ⟨7, 7, 6⟩, ⟨4, 7, 2⟩, ⟨7, 8, 5⟩, ⟨7, 7, 7⟩, ⟨7, 8, 6⟩, ⟨4, 7, 1⟩, ⟨7, 8, 7⟩, ⟨4, 7, 3⟩, ⟨7, 7, 5⟩, ⟨4, 7, 0⟩, ⟨7, 7, 4⟩, ⟨7, 8, 4⟩,
   ⟨5, 2, 5⟩, ⟨5, 4, 7⟩, ⟨5, 3, 6⟩, ⟨5, 2, 4⟩, ⟨5, 3, 4⟩, ⟨5, 4, 4⟩, ⟨5, 3, 5⟩, ⟨5, 4, 6⟩, ⟨5, 2, 7⟩, ⟨5, 4, 5⟩, ⟨5, 2, 6⟩, ⟨5, 3, 7⟩,
   ⟨5, 5, 0⟩, ⟨5, 6, 0⟩, ⟨4, 6, 4⟩, ⟨5, 5, 1⟩, ⟨4, 6, 7⟩, ⟨5, 6, 3⟩, ⟨4, 6, 6⟩, ⟨5, 6, 1⟩, ⟨5, 5, 2⟩, ⟨5, 6, 2⟩, ⟨5, 5, 3⟩, ⟨4, 6, 5⟩,
   ⟨1, 2, 5⟩, ⟨1, 3, 6⟩, ⟨1, 4, 7⟩, ⟨1, 2, 4⟩, ⟨1, 4, 4⟩, ⟨1, 3, 4⟩, ⟨1, 4, 5⟩, ⟨1, 3, 7⟩, ⟨1, 2, 6⟩, ⟨1, 3, 5⟩, ⟨1, 2, 7⟩, ⟨1, 4, 6⟩,
   ⟨6, 7, 7⟩, ⟨5, 7, 1⟩, ⟨6, 8, 6⟩, ⟨6, 7, 6⟩, ⟨6, 8, 5⟩, ⟨5, 7, 2⟩, ⟨6, 8, 4⟩, ⟨5, 7, 0⟩, ⟨6, 7, 4⟩, ⟨5, 7, 3⟩, ⟨6, 7, 5⟩, ⟨6, 8, 7⟩,
   ⟨1, 7, 1⟩, ⟨3, 8, 6⟩, ⟨3, 7, 7⟩, ⟨1, 7, 0⟩, ⟨3, 7, 4⟩, ⟨3, 8, 4⟩, ⟨3, 7, 5⟩, ⟨3, 8, 7⟩, ⟨1, 7, 3⟩, ⟨3, 8, 5⟩, ⟨1, 7, 2⟩, ⟨3, 7, 6⟩,
   ⟨6, 2, 6⟩, ⟨6, 4, 5⟩, ⟨6, 3, 7⟩, ⟨6, 2, 7⟩, ⟨6, 3, 5⟩, ⟨6, 4, 6⟩, ⟨6, 3, 4⟩, ⟨6, 4, 4⟩, ⟨6, 2, 4⟩, ⟨6, 4, 7⟩, ⟨6, 2, 5⟩, ⟨6, 3, 6⟩,
   ⟨2, 7, 2⟩, ⟨2, 8, 1⟩, ⟨0, 7, 6⟩, ⟨2, 7, 3⟩, ⟨0, 7, 5⟩, ⟨2, 8, 2⟩, ⟨0, 7, 4⟩, ⟨2, 8, 0⟩, ⟨2, 7, 0⟩, ⟨2, 8, 3⟩, ⟨2, 7, 1⟩, ⟨0, 7, 7⟩,
   ⟨5, 7, 5⟩, ⟨6, 7, 3⟩, ⟨6, 8, 2⟩, ⟨5, 7, 4⟩, ⟨6, 8, 0⟩, ⟨6, 7, 0⟩, ⟨6, 8, 1⟩, ⟨6, 7, 2⟩, ⟨5, 7, 6⟩, ⟨6, 7, 1⟩, ⟨5, 7, 7⟩, ⟨6, 8, 3⟩,
   ⟨2, 2, 7⟩, ⟨2, 3, 5⟩, ⟨2, 4, 6⟩, ⟨2, 2, 6⟩, ⟨2, 4, 5⟩, ⟨2, 3, 7⟩, ⟨2, 4, 4⟩, ⟨2, 3, 4⟩, ⟨2, 2, 4⟩, ⟨2, 3, 6⟩, ⟨2, 2, 5⟩, ⟨2, 4, 7⟩,
   ⟨7, 5, 6⟩, ⟨6, 6, 2⟩, ⟨7, 6, 5⟩, ⟨7, 5, 7⟩, ⟨7, 6, 6⟩, ⟨6, 6, 1⟩, ⟨7, 6, 7⟩, ⟨6, 6, 3⟩, ⟨7, 5, 5⟩, ⟨6, 6, 0⟩, ⟨7, 5, 4⟩, ⟨7, 6, 4⟩,
   ⟨7, 2, 7⟩, ⟨7, 4, 6⟩, ⟨7, 3, 5⟩, ⟨7, 2, 6⟩, ⟨7, 3, 7⟩, ⟨7, 4, 5⟩, ⟨7, 3, 6⟩, ⟨7, 4, 7⟩, ⟨7, 2, 5⟩, ⟨7, 4, 4⟩, ⟨7, 2, 4⟩, ⟨7, 3, 4⟩,
   ⟨4, 7, 4⟩, ⟨7, 7, 0⟩, ⟨7, 8, 0⟩, ⟨4, 7, 5⟩, ⟨7, 8, 2⟩, ⟨7, 7, 3⟩, ⟨7, 8, 3⟩, ⟨7, 7, 1⟩, ⟨4, 7, 7⟩, ⟨7, 7, 2⟩, ⟨4, 7, 6⟩, ⟨7, 8, 1⟩,
   ⟨3, 7, 3⟩, ⟨3, 8, 2⟩, ⟨1, 7, 5⟩, ⟨3, 7, 2⟩, ⟨1, 7, 6⟩, ⟨3, 8, 1⟩, ⟨1, 7, 7⟩, ⟨3, 8, 3⟩, ⟨3, 7, 1⟩, ⟨3, 8, 0⟩, ⟨3, 7, 0⟩, ⟨1, 7, 4⟩,
   ⟨7, 5, 2⟩, ⟨7, 6, 1⟩, ⟨6, 6, 6⟩, ⟨7, 5, 3⟩, ⟨6, 6, 5⟩, ⟨7, 6, 2⟩, ⟨6, 6, 4⟩, ⟨7, 6, 0⟩, ⟨7, 5, 0⟩, ⟨7, 6, 3⟩, ⟨7, 5, 1⟩, ⟨6, 6, 7⟩,
   ⟨3, 2, 6⟩, ⟨3, 3, 7⟩, ⟨3, 4, 5⟩, ⟨3, 2, 7⟩, ⟨3, 4, 6⟩, ⟨3, 3, 5⟩, ⟨3, 4, 7⟩, ⟨3, 3, 6⟩, ⟨3, 2, 5⟩, ⟨3, 3, 4⟩, ⟨3, 2, 4⟩, ⟨3, 4, 4⟩]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem certificate : List.Forall₂
    (fun g (t : Fin 8 × Fin 9 × Fin 8) =>
      g = ((upper t.1 * rep t.2.1 * upper t.2.2 : A6) : S6)) allEven factors := by
  decide +kernel

private theorem left_exists {α β : Type*} {R : α → β → Prop} {l : List α} {m : List β}
    (h : List.Forall₂ R l m) {a : α} (ha : a ∈ l) : ∃ b, R a b := by
  induction h with
  | nil => simp at ha
  | @cons x y xs ys hxy h ih =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨y, hxy⟩
    · exact ih ha

private theorem decomposition (g : A6) : ∃ i j k, g = upper i * rep j * upper k := by
  have hg : (g : S6) ∈ allEven := by
    apply List.mem_filter.mpr
    refine ⟨?_, by simpa only [decide_eq_true_eq] using (show Equiv.Perm.sign (g : S6) = 1 from g.property)⟩
    apply mem_permsOfList_of_mem
    intro x _
    fin_cases x <;> simp
  obtain ⟨⟨i, j, k⟩, h⟩ := left_exists certificate hg
  exact ⟨i, j, k, Subtype.ext h⟩

private theorem upper_mem (i : Fin 8) : upper i ∈ a6Borel := by
  revert i
  decide +kernel

private def generators (j : Fin 9) : Fin 9 → A6 :=
  fun i => if h : i.val < 8 then upper ⟨i.val, h⟩ else rep j
private def aWords : Fin 9 → List (Fin 9) :=
  ![[],
    [8,4],
    [7,8,3,8,2,8],
    [5,8,2,8,1,8],
    [6,8,1,8,3,8],
    [],
    [8,8,8,1,8],
    [4,8,2,8,4],
    [4,8,1,8,8,2,8]]
private def bWords : Fin 9 → List (Fin 9) :=
  ![[],
    [],
    [8,5,8],
    [2,8,1,8,5,8],
    [3,8,1,8,5,8],
    [8],
    [2,8,1,8,8,8,2],
    [7,8,5,8,4,8],
    [2,8,8,8,1,8,7]]

private theorem a_certificate : ∀ j : Fin 9,
    rep j ∈ a6SynthemeStabilizer ∨ ((aWords j).map (generators j)).prod = a := by
  decide +kernel
private theorem b_certificate : ∀ j : Fin 9,
    rep j ∈ a6DuadStabilizer ∨ ((bWords j).map (generators j)).prod = b := by
  decide +kernel

private theorem word_mem (H : Subgroup A6) (hB : a6Borel ≤ H)
    (j : Fin 9) (hj : rep j ∈ H) (w : List (Fin 9)) :
    (w.map (generators j)).prod ∈ H := by
  apply H.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  dsimp [generators]
  split
  · exact hB (upper_mem _)
  · exact hj

private def fullGenerators : Fin 10 → A6 :=
  fun i => if h : i.val < 8 then upper ⟨i.val, h⟩ else if i.val = 8 then a else b
private def repWords : Fin 9 → List (Fin 10) :=
  ![[],
    [8,4],
    [2,9,8,9,2],
    [2,9,8,9,6,8],
    [2,9,8,9,8,5],
    [9],
    [9,8,4],
    [8,5,9,8],
    [8,4,9]]
private theorem rep_certificate : ∀ j : Fin 9,
    ((repWords j).map fullGenerators).prod = rep j := by decide +kernel

private theorem eq_top (H : Subgroup A6) (hB : a6Borel ≤ H)
    (ha : a ∈ H) (hb : b ∈ H) : H = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨i, j, k, rfl⟩ := decomposition g
  apply H.mul_mem (H.mul_mem (hB (upper_mem i)) _) (hB (upper_mem k))
  rw [← rep_certificate j]
  apply H.list_prod_mem
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  dsimp [fullGenerators]
  split
  · exact hB (upper_mem _)
  · split
    · exact ha
    · exact hb
end Certificate

namespace Certificate
private theorem a_mem_of_not_le (H : Subgroup A6) (hB : a6Borel ≤ H)
    (hP : ¬ H ≤ a6SynthemeStabilizer) : a ∈ H := by
  obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hP
  obtain ⟨i, j, k, h⟩ := decomposition g
  have hi := hB (upper_mem i)
  have hk := hB (upper_mem k)
  have hj : rep j ∈ H :=
    (H.mul_mem_cancel_left hi).mp ((H.mul_mem_cancel_right hk).mp (h ▸ hg))
  rcases a_certificate j with hp | hw
  · apply (hgp _).elim
    rw [h]
    exact a6SynthemeStabilizer.mul_mem
      (a6SynthemeStabilizer.mul_mem (upper_mem i).2 hp) (upper_mem k).2
  · rw [← hw]
    exact word_mem H hB j hj _

private theorem b_mem_of_not_le (H : Subgroup A6) (hB : a6Borel ≤ H)
    (hP : ¬ H ≤ a6DuadStabilizer) : b ∈ H := by
  obtain ⟨g, hg, hgp⟩ := SetLike.not_le_iff_exists.mp hP
  obtain ⟨i, j, k, h⟩ := decomposition g
  have hi := hB (upper_mem i)
  have hk := hB (upper_mem k)
  have hj : rep j ∈ H :=
    (H.mul_mem_cancel_left hi).mp ((H.mul_mem_cancel_right hk).mp (h ▸ hg))
  rcases b_certificate j with hp | hw
  · apply (hgp _).elim
    rw [h]
    exact a6DuadStabilizer.mul_mem
      (a6DuadStabilizer.mul_mem (upper_mem i).1 hp) (upper_mem k).1
  · rw [← hw]
    exact word_mem H hB j hj _
end Certificate

theorem a6_overgroup_borel (H : Subgroup A6) (hB : a6Borel ≤ H) (hH : H ≠ ⊤) :
    H ≤ a6DuadStabilizer ∨ H ≤ a6SynthemeStabilizer := by
  classical
  by_contra h
  obtain ⟨hp, hl⟩ := not_or.mp h
  exact hH (Certificate.eq_top H hB (Certificate.a_mem_of_not_le H hB hl)
    (Certificate.b_mem_of_not_le H hB hp))

private theorem le_of_comap_le (H K : Subgroup S6)
    (hH : Equiv.swap 0 1 ∈ H) (hK : Equiv.swap 0 1 ∈ K)
    (h : H.comap A6.subtype ≤ K.comap A6.subtype) : H ≤ K := by
  intro g hg
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with heven | hodd
  · exact h (show (⟨g, heven⟩ : A6) ∈ H.comap A6.subtype from hg)
  · have hs : Equiv.Perm.sign (Equiv.swap 0 1 * g) = 1 := by
      rw [map_mul, hodd, Equiv.Perm.sign_swap (by decide)]
      decide
    have hx : Equiv.swap 0 1 * g ∈ K :=
      h (show (⟨Equiv.swap 0 1 * g, hs⟩ : A6) ∈ H.comap A6.subtype from H.mul_mem hH hg)
    simpa only [← mul_assoc, Equiv.swap_mul_self, one_mul] using K.mul_mem hK hx

theorem overgroup_borel (H : Subgroup S6) (hB : borel ≤ H) (hH : H ≠ ⊤) :
    H ≤ duadStabilizer ∨ H ≤ synthemeStabilizer := by
  have ht : Equiv.swap 0 1 ∈ H := hB (by decide)
  have hA : H.comap A6.subtype ≠ ⊤ := by
    intro h
    apply hH
    apply top_unique
    apply le_of_comap_le ⊤ H (by trivial) ht
    rw [h]
    exact le_top
  have hb : a6Borel ≤ H.comap A6.subtype := Subgroup.comap_mono hB
  rcases a6_overgroup_borel _ hb hA with hp | hq
  · exact Or.inl (le_of_comap_le H duadStabilizer ht (by decide) hp)
  · exact Or.inr (le_of_comap_le H synthemeStabilizer ht (by decide) hq)


theorem duadStabilizer_not_le_syntheme : ¬ duadStabilizer ≤ synthemeStabilizer := by
  intro h
  exact (by decide : (Certificate.a : S6) ∉ synthemeStabilizer) (h (by decide : (Certificate.a : S6) ∈ duadStabilizer))

theorem synthemeStabilizer_not_le_duad : ¬ synthemeStabilizer ≤ duadStabilizer := by
  intro h
  exact (by decide : (Certificate.b : S6) ∉ duadStabilizer) (h (by decide : (Certificate.b : S6) ∈ synthemeStabilizer))

theorem parabolics_ne : duadStabilizer ≠ synthemeStabilizer :=
  fun h => duadStabilizer_not_le_syntheme h.le

theorem duadStabilizer_ne_top : duadStabilizer ≠ ⊤ :=
  fun h => synthemeStabilizer_not_le_duad (h.symm ▸ le_top)

theorem synthemeStabilizer_ne_top : synthemeStabilizer ≠ ⊤ :=
  fun h => duadStabilizer_not_le_syntheme (h.symm ▸ le_top)

theorem duadStabilizer_isCoatom : IsCoatom duadStabilizer := by
  refine ⟨duadStabilizer_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases overgroup_borel H (le_trans borel_le_duadStabilizer hH.le) hn with hp | hl
  · exact hH.not_ge hp
  · exact duadStabilizer_not_le_syntheme (hH.le.trans hl)

theorem synthemeStabilizer_isCoatom : IsCoatom synthemeStabilizer := by
  refine ⟨synthemeStabilizer_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases overgroup_borel H (le_trans borel_le_synthemeStabilizer hH.le) hn with hp | hl
  · exact synthemeStabilizer_not_le_duad (hH.le.trans hp)
  · exact hH.not_ge hl

/-- Exactly the two standard parabolics are maximal over the flag stabilizer. -/
theorem coatoms_over_borel (H : Subgroup S6) :
    IsCoatom H ∧ borel ≤ H ↔ H = duadStabilizer ∨ H = synthemeStabilizer := by
  constructor
  · rintro ⟨hH, hB⟩
    rcases overgroup_borel H hB hH.1 with hp | hl
    · exact Or.inl (eq_of_le_of_not_lt hp (fun h => duadStabilizer_ne_top (hH.2 _ h)))
    · exact Or.inr (eq_of_le_of_not_lt hl (fun h => synthemeStabilizer_ne_top (hH.2 _ h)))
  · rintro (rfl | rfl)
    · exact ⟨duadStabilizer_isCoatom, borel_le_duadStabilizer⟩
    · exact ⟨synthemeStabilizer_isCoatom, borel_le_synthemeStabilizer⟩

theorem parabolics_sup : duadStabilizer ⊔ synthemeStabilizer = ⊤ := by
  apply duadStabilizer_isCoatom.2
  exact lt_of_le_of_ne le_sup_left
    (fun h => synthemeStabilizer_not_le_duad (sup_eq_left.mp h.symm))

/-- Conjugation gives the exhaustive pair of maximal overgroups of any Sylow
 two-subgroup, in the actual permutation group. -/
theorem coatoms_over_sylow (T : Sylow 2 S6) :
    ∃ g : S6, (MulAut.conj g).mapSubgroup borel = (T : Subgroup S6) ∧
      ∀ H : Subgroup S6, (IsCoatom H ∧ (T : Subgroup S6) ≤ H) ↔
        H = (MulAut.conj g).mapSubgroup duadStabilizer ∨
        H = (MulAut.conj g).mapSubgroup synthemeStabilizer := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S6 borelSylow T
  let e := (MulAut.conj g).mapSubgroup
  have he : e borel = (T : Subgroup S6) := by
    change ((g • borelSylow : Sylow 2 S6) : Subgroup S6) = (T : Subgroup S6)
    rw [hg]
  refine ⟨g, he, ?_⟩
  intro H
  constructor
  · rintro ⟨hH, hTH⟩
    have hc : IsCoatom (e.symm H) := (e.symm.isCoatom_iff H).2 hH
    have hb : borel ≤ e.symm H := by
      have hh := e.symm.monotone hTH
      rwa [← he, e.symm_apply_apply] at hh
    rcases (coatoms_over_borel (e.symm H)).mp ⟨hc, hb⟩ with h | h
    · left
      exact (e.apply_symm_apply H).symm.trans (congrArg e h)
    · right
      exact (e.apply_symm_apply H).symm.trans (congrArg e h)
  · rintro (rfl | rfl)
    · exact ⟨(e.isCoatom_iff _).2 duadStabilizer_isCoatom,
        he ▸ e.monotone borel_le_duadStabilizer⟩
    · exact ⟨(e.isCoatom_iff _).2 synthemeStabilizer_isCoatom,
        he ▸ e.monotone borel_le_synthemeStabilizer⟩

theorem a6DuadStabilizer_not_le_syntheme : ¬ a6DuadStabilizer ≤ a6SynthemeStabilizer := by
  intro h
  exact (by decide : Certificate.a ∉ a6SynthemeStabilizer) (h (by decide : Certificate.a ∈ a6DuadStabilizer))

theorem a6SynthemeStabilizer_not_le_duad : ¬ a6SynthemeStabilizer ≤ a6DuadStabilizer := by
  intro h
  exact (by decide : Certificate.b ∉ a6DuadStabilizer) (h (by decide : Certificate.b ∈ a6SynthemeStabilizer))

theorem a6_parabolics_ne : a6DuadStabilizer ≠ a6SynthemeStabilizer :=
  fun h => a6DuadStabilizer_not_le_syntheme h.le

theorem a6DuadStabilizer_ne_top : a6DuadStabilizer ≠ ⊤ :=
  fun h => a6SynthemeStabilizer_not_le_duad (h.symm ▸ le_top)

theorem a6SynthemeStabilizer_ne_top : a6SynthemeStabilizer ≠ ⊤ :=
  fun h => a6DuadStabilizer_not_le_syntheme (h.symm ▸ le_top)

theorem a6DuadStabilizer_isCoatom : IsCoatom a6DuadStabilizer := by
  refine ⟨a6DuadStabilizer_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases a6_overgroup_borel H (le_trans a6Borel_le_duadStabilizer hH.le) hn with hp | hl
  · exact hH.not_ge hp
  · exact a6DuadStabilizer_not_le_syntheme (hH.le.trans hl)

theorem a6SynthemeStabilizer_isCoatom : IsCoatom a6SynthemeStabilizer := by
  refine ⟨a6SynthemeStabilizer_ne_top, ?_⟩
  intro H hH
  by_contra hn
  rcases a6_overgroup_borel H (le_trans a6Borel_le_synthemeStabilizer hH.le) hn with hp | hl
  · exact a6SynthemeStabilizer_not_le_duad (hH.le.trans hp)
  · exact hH.not_ge hl

/-- Exactly the two standard parabolics are maximal over the flag stabilizer. -/
theorem a6_coatoms_over_borel (H : Subgroup A6) :
    IsCoatom H ∧ a6Borel ≤ H ↔ H = a6DuadStabilizer ∨ H = a6SynthemeStabilizer := by
  constructor
  · rintro ⟨hH, hB⟩
    rcases a6_overgroup_borel H hB hH.1 with hp | hl
    · exact Or.inl (eq_of_le_of_not_lt hp (fun h => a6DuadStabilizer_ne_top (hH.2 _ h)))
    · exact Or.inr (eq_of_le_of_not_lt hl (fun h => a6SynthemeStabilizer_ne_top (hH.2 _ h)))
  · rintro (rfl | rfl)
    · exact ⟨a6DuadStabilizer_isCoatom, a6Borel_le_duadStabilizer⟩
    · exact ⟨a6SynthemeStabilizer_isCoatom, a6Borel_le_synthemeStabilizer⟩

theorem a6_parabolics_sup : a6DuadStabilizer ⊔ a6SynthemeStabilizer = ⊤ := by
  apply a6DuadStabilizer_isCoatom.2
  exact lt_of_le_of_ne le_sup_left
    (fun h => a6SynthemeStabilizer_not_le_duad (sup_eq_left.mp h.symm))

/-- Conjugation gives the exhaustive pair of maximal overgroups of any Sylow
 two-subgroup, in the actual permutation group. -/
theorem a6_coatoms_over_sylow (T : Sylow 2 A6) :
    ∃ g : A6, (MulAut.conj g).mapSubgroup a6Borel = (T : Subgroup A6) ∧
      ∀ H : Subgroup A6, (IsCoatom H ∧ (T : Subgroup A6) ≤ H) ↔
        H = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
        H = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A6 a6BorelSylow T
  let e := (MulAut.conj g).mapSubgroup
  have he : e a6Borel = (T : Subgroup A6) := by
    change ((g • a6BorelSylow : Sylow 2 A6) : Subgroup A6) = (T : Subgroup A6)
    rw [hg]
  refine ⟨g, he, ?_⟩
  intro H
  constructor
  · rintro ⟨hH, hTH⟩
    have hc : IsCoatom (e.symm H) := (e.symm.isCoatom_iff H).2 hH
    have hb : a6Borel ≤ e.symm H := by
      have hh := e.symm.monotone hTH
      rwa [← he, e.symm_apply_apply] at hh
    rcases (a6_coatoms_over_borel (e.symm H)).mp ⟨hc, hb⟩ with h | h
    · left
      exact (e.apply_symm_apply H).symm.trans (congrArg e h)
    · right
      exact (e.apply_symm_apply H).symm.trans (congrArg e h)
  · rintro (rfl | rfl)
    · exact ⟨(e.isCoatom_iff _).2 a6DuadStabilizer_isCoatom,
        he ▸ e.monotone a6Borel_le_duadStabilizer⟩
    · exact ⟨(e.isCoatom_iff _).2 a6SynthemeStabilizer_isCoatom,
        he ▸ e.monotone a6Borel_le_synthemeStabilizer⟩

end Theory.SpecificGroups.SymmetricSix
