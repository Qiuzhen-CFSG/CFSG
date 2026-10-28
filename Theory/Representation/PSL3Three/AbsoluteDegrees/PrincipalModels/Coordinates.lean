module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Geometry

/-!
# Explicit coordinates for the PSL₃(3) geometric models

The thirteen normalized nonzero vectors enumerate the actual projective
points, and the fifty-two incident pairs enumerate the actual flags.
Kernel-checked finite identities compute the point, inverse-transpose line,
and flag permutations of two specified determinant-one matrices. These are
identities for the native quotient-group action, not an abstract group tag
or a presentation assumed to define PSL₃(3). No generation assertion is needed
to use these actors in a density proof.

The tables are calculated directly over ZMod 3. They support the two geometric
models used in GM02, Proposition 4.2, manuscript pp.9--10; no external action
matrices or character tables enter their proofs.
-/

@[expose] public section

namespace Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Coordinates
open Configuration
open scoped Matrix

abbrev PG := PrincipalModels.PG
abbrev Flag := PrincipalModels.Flag

/-- Representatives normalized by their first nonzero coordinate. -/
def pointVector : Fin 13 → Fin 3 → ZMod 3 :=
  ![![0, 0, 1], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2]]

lemma pointVector_ne_zero : ∀ i, pointVector i ≠ 0 := by decide +kernel

lemma normalized_unique : ∀ (i j : Fin 13) (a : ZMod 3),
    a • pointVector j = pointVector i → i = j := by decide +kernel

def pointAt (i : Fin 13) : PG :=
  Projectivization.mk (ZMod 3) (pointVector i) (pointVector_ne_zero i)

lemma pointAt_injective : Function.Injective pointAt := by
  intro i j h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' (ZMod 3)
    _ _ (pointVector_ne_zero i) (pointVector_ne_zero j)).mp h
  exact normalized_unique i j a ha

noncomputable def pointEquiv : Fin 13 ≃ PG :=
  _root_.Equiv.ofBijective pointAt ((Fintype.bijective_iff_injective_and_card pointAt).mpr
    ⟨pointAt_injective, by simp [PrincipalModels.card_points]⟩)

@[simp] lemma pointEquiv_apply (i : Fin 13) : pointEquiv i = pointAt i := rfl

lemma incident_iff (i j : Fin 13) : pointAt i ∈ pointAt j ↔
    pointVector i ⬝ᵥ pointVector j = 0 := by
  simp only [pointAt, Configuration.ofField.mem_iff, Projectivization.orthogonal_mk]

/-- Two actual determinant-one matrices; generation of the whole group is not needed. -/
def generatorSL : Fin 2 → Matrix.PSL3Three.SL :=
  ![⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
    ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by decide⟩]

def actor (a : Fin 2) : PrincipalModels.Group := Matrix.PSL3Three.project (generatorSL a)

def pointImage : Fin 2 → Fin 13 → Fin 13 :=
  ![![0, 7, 8, 9, 4, 5, 6, 10, 12, 11, 1, 3, 2], ![4, 0, 5, 6, 1, 7, 10, 2, 8, 12, 3, 9, 11]]

def lineImage : Fin 2 → Fin 13 → Fin 13 :=
  ![![0, 1, 2, 3, 10, 11, 12, 4, 5, 6, 7, 8, 9], ![4, 0, 5, 6, 1, 7, 10, 2, 8, 12, 3, 9, 11]]

lemma point_action_data : ∀ (a : Fin 2) (i : Fin 13), ∃ c : ZMod 3,
    c • pointVector (pointImage a i) = (generatorSL a).val *ᵥ pointVector i := by
  decide +kernel

lemma line_action_data : ∀ (a : Fin 2) (i : Fin 13), ∃ c : ZMod 3,
    c • pointVector (lineImage a i) =
      (Matrix.SpecialLinearGroup.inverseTranspose (generatorSL a)).val *ᵥ pointVector i := by
  decide +kernel

lemma pointPerm_actor (a : Fin 2) (i : Fin 13) :
    pointPerm (actor a) (pointAt i) = pointAt (pointImage a i) := by
  rw [pointPerm_apply]
  change (generatorSL a) • Projectivization.mk (ZMod 3) (pointVector i) (pointVector_ne_zero i) = _
  rw [Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr
  exact point_action_data a i

lemma linePerm_actor (a : Fin 2) (i : Fin 13) :
    linePerm (actor a) (pointAt i) = pointAt (lineImage a i) := by
  rw [actor, linePerm_project]
  change (Matrix.SpecialLinearGroup.inverseTranspose (generatorSL a)) •
    Projectivization.mk (ZMod 3) (pointVector i) (pointVector_ne_zero i) = _
  rw [Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff' (ZMod 3) _ _ _ _).mpr
  exact line_action_data a i

def flagPair : Fin 52 → Fin 13 × Fin 13 :=
  ![(0, 1), (0, 4), (0, 7), (0, 10), (1, 0), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 9), (2, 11), (3, 2), (3, 4), (3, 8), (3, 12), (4, 0), (4, 1), (4, 2), (4, 3), (5, 1), (5, 6), (5, 9), (5, 12), (6, 1), (6, 5), (6, 8), (6, 11), (7, 0), (7, 10), (7, 11), (7, 12), (8, 3), (8, 6), (8, 8), (8, 10), (9, 2), (9, 5), (9, 9), (9, 10), (10, 0), (10, 7), (10, 8), (10, 9), (11, 2), (11, 6), (11, 7), (11, 11), (12, 3), (12, 5), (12, 7), (12, 12)]

lemma flagPair_incident : ∀ i,
    pointVector (flagPair i).1 ⬝ᵥ pointVector (flagPair i).2 = 0 := by decide +kernel

lemma flagPair_injective : Function.Injective flagPair := by decide +kernel

def flagAt (i : Fin 52) : Flag :=
  ⟨(pointAt (flagPair i).1, pointAt (flagPair i).2),
    (incident_iff _ _).mpr (flagPair_incident i)⟩

lemma flagAt_injective : Function.Injective flagAt := by
  intro i j h
  apply flagPair_injective
  have hp := congrArg (fun f : Flag => f.val.1) h
  have hl := congrArg (fun f : Flag => f.val.2) h
  exact Prod.ext (pointAt_injective hp) (pointAt_injective hl)

noncomputable def flagEquiv : Fin 52 ≃ Flag :=
  _root_.Equiv.ofBijective flagAt ((Fintype.bijective_iff_injective_and_card flagAt).mpr
    ⟨flagAt_injective, by simp [PrincipalModels.card_flags]⟩)

@[simp] lemma flagEquiv_apply (i : Fin 52) : flagEquiv i = flagAt i := rfl

def flagImage : Fin 2 → Fin 52 → Fin 52 :=
  ![![0, 3, 1, 2, 28, 29, 30, 31, 32, 35, 33, 34, 36, 39, 37, 38, 16, 17, 18, 19, 20, 23, 21, 22, 24, 27, 25, 26, 40, 41, 42, 43, 48, 51, 49, 50, 44, 47, 45, 46, 4, 5, 6, 7, 12, 15, 13, 14, 8, 11, 9, 10], ![16, 17, 18, 19, 1, 0, 2, 3, 21, 20, 23, 22, 25, 24, 26, 27, 5, 4, 6, 7, 28, 29, 31, 30, 40, 41, 42, 43, 9, 8, 10, 11, 33, 35, 34, 32, 49, 50, 51, 48, 13, 12, 14, 15, 37, 39, 36, 38, 45, 46, 44, 47]]

lemma flag_action_data : ∀ (a : Fin 2) (i : Fin 52),
    (pointImage a (flagPair i).1, lineImage a (flagPair i).2) =
      flagPair (flagImage a i) := by decide +kernel

lemma flagPerm_actor (a : Fin 2) (i : Fin 52) :
    flagPerm (actor a) (flagAt i) = flagAt (flagImage a i) := by
  apply Subtype.ext
  change (pointPerm (actor a) (pointAt (flagPair i).1),
    linePerm (actor a) (pointAt (flagPair i).2)) = _
  rw [pointPerm_actor, linePerm_actor]
  have h := flag_action_data a i
  exact Prod.ext (congrArg pointAt (congrArg Prod.fst h))
    (congrArg pointAt (congrArg Prod.snd h))

end Representation.PSL3Three.AbsoluteDegrees.PrincipalModels.Coordinates
