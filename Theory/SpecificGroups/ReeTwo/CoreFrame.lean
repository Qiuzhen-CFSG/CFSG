module

public import Theory.SpecificGroups.ReeTwo.Relations
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.NormNum

/-!
# A four-generator frame for the Ree core table

Besides the fixed root t and the central involution z, a frame chooses four
elements a. The next four roots are their commutators with t. Thus only four
new elements need to be constructed. The square map, six upper commutators,
and the pairing with the four derived roots are the remaining coordinate
conditions. Elementary abelianness of the derived layer and centralization
by t supply the rest of the table.

This is a verification lemma, not an existence or recognition theorem.
The ordering and right-commutator convention are those of Shinoda (1975),
(2.3), pp.81–82, specialized to q = 2.
-/

@[expose] public section
namespace ReeTwo

/-- The four derived roots forced by the fixed root and a frame. -/
def frameTail {H : Type*} [Group H] (a : Fin 4 → H) (t : H) : Fin 4 → H :=
  ![rightComm (a 0) t, rightComm (a 1) t,
    rightComm t (a 2), rightComm t (a 3)]

/-- Insert a frame and its forced derived roots into Shinoda's root order. -/
def frameRoots {H : Type*} [Group H] (a : Fin 4 → H) (t z : H) : CoreRoot → H :=
  ![a 0, a 1, t, a 2, a 3, frameTail a t 0, frameTail a t 1,
    frameTail a t 2, frameTail a t 3, z]

/-- The coordinate conditions not supplied by the elementary derived layer.
Existence of a frame with these conditions is a separate obligation. -/
structure FrameCoordinates {H : Type*} [Group H] (a : Fin 4 → H) (t z : H) : Prop where
  square : ∀ i, a i * a i = (![1, frameTail a t 0, frameTail a t 3, 1] : Fin 4 → H) i
  comm01 : rightComm (a 0) (a 1) = 1
  comm02 : rightComm (a 0) (a 2) = frameTail a t 0 * frameTail a t 1 * z
  comm03 : rightComm (a 0) (a 3) = frameTail a t 1 * frameTail a t 2
  comm12 : rightComm (a 1) (a 2) = 1
  comm13 : rightComm (a 1) (a 3) = frameTail a t 2 * frameTail a t 3 * z
  comm23 : rightComm (a 2) (a 3) = 1
  pairing : ∀ i j, rightComm (a i) (frameTail a t j) = if i.val + j.val = 3 then z else 1

/-- A frame with an elementary commuting tail gives the entire ten-root table. -/
theorem coreRelations_frameRoots {H : Type*} [Group H]
    (a : Fin 4 → H) (t z : H) (h : FrameCoordinates a t z)
    (ht : t * t = z) (hz : z * z = 1)
    (htail : ∀ i, frameTail a t i * frameTail a t i = 1)
    (htailcomm : ∀ i j, rightComm (frameTail a t i) (frameTail a t j) = 1)
    (httail : ∀ i, rightComm t (frameTail a t i) = 1)
    (haz : ∀ i, rightComm (a i) z = 1)
    (htz : rightComm t z = 1)
    (htailz : ∀ i, rightComm (frameTail a t i) z = 1) :
    CoreRelations (frameRoots a t z) := by
  constructor
  · intro i
    fin_cases i
    · simpa [frameRoots, coreSquare, rootWord] using h.square 0
    · simpa [frameRoots, coreSquare, rootWord] using h.square 1
    · simpa [frameRoots, coreSquare, rootWord] using ht
    · simpa [frameRoots, coreSquare, rootWord] using h.square 2
    · simpa [frameRoots, coreSquare, rootWord] using h.square 3
    · simpa [frameRoots, coreSquare, rootWord] using htail 0
    · simpa [frameRoots, coreSquare, rootWord] using htail 1
    · simpa [frameRoots, coreSquare, rootWord] using htail 2
    · simpa [frameRoots, coreSquare, rootWord] using htail 3
    · simpa [frameRoots, coreSquare, rootWord] using hz
  · intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij
    all_goals simp [frameRoots, coreCommutator, rootWord, mul_assoc,
      h.comm01, h.comm02, h.comm03, h.comm12, h.comm13, h.comm23,
      h.pairing, htailcomm, httail, haz, htz, htailz]
    all_goals rfl

private theorem rightComm_of_commuting {H : Type*} [Group H]
    (a b : H) (h : a * b = b * a) : rightComm a b = 1 := by
  unfold rightComm
  calc
    _ = (b * a)⁻¹ * (a * b) := by group
    _ = 1 := by rw [h, inv_mul_cancel]

private theorem rightComm_mem_derived {H : Type*} [Group H] (a b : H) :
    rightComm a b ∈ commutator H := by
  simpa [rightComm, commutatorElement_def, commutator] using
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top a⁻¹) (Subgroup.mem_top b⁻¹))

/-- In a group with elementary derived subgroup, the derived tail relations
are automatic once the fixed root centralizes that layer. -/
theorem coreRelations_frameRoots_of_elementary {H : Type*} [Group H]
    (D : Subgroup H) [IsElementaryAbelian 2 D]
    (hD : commutator H ≤ D) (a : Fin 4 → H) (t z : H)
    (hframe : FrameCoordinates a t z)
    (htD : t ∈ Subgroup.centralizer (D : Set H))
    (hzZ : z ∈ Subgroup.center H) (ht : t ^ 2 = z) (hz : z ^ 2 = 1) :
    CoreRelations (frameRoots a t z) := by
  have htail : ∀ i, frameTail a t i ∈ D := by
    intro i
    fin_cases i <;> exact hD (rightComm_mem_derived _ _)
  have hzH : ∀ q : H, q * z = z * q := Subgroup.mem_center_iff.mp hzZ
  apply coreRelations_frameRoots a t z hframe
  · simpa only [pow_two] using ht
  · simpa only [pow_two] using hz
  · intro i
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian
      (p := 2) (frameTail a t i) (htail i)
  · intro i j
    apply rightComm_of_commuting
    exact congrArg Subtype.val
      (mul_comm' (⟨_, htail i⟩ : D) ⟨_, htail j⟩)
  · intro i
    exact rightComm_of_commuting _ _ (Subgroup.mem_centralizer_iff.mp htD _ (htail i)).symm
  · intro i
    exact rightComm_of_commuting _ _ (hzH _)
  · exact rightComm_of_commuting _ _ (hzH _)
  · intro i
    exact rightComm_of_commuting _ _ (hzH _)

end ReeTwo
