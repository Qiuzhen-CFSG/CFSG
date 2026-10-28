module

public import Theory.GroupTheory.WordSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Word coordinates for E₉ × A₄

Two cyclic generators and a double transposition and three-cycle give 108
normal forms. The finite permutation calculations below certify a bijection
with the actual product of ZMod groups and the alternating group, including
its right-generator transition table. In any target group, verifying those
transitions suffices to construct a homomorphism; separating the normal forms
makes it injective.

This supports the E₉ × A₄ subgroup used in Aschbacher--Smith, *The
Classification of Quasithin Groups*, A.2.19, printed p. 41. It asserts no
embedding in a particular sporadic group without the target calculations.
-/

@[expose] public section

open Theory.GroupTheory
namespace Theory.SpecificGroups.E9A4
abbrev Source := Multiplicative (ZMod 3 × ZMod 3) × alternatingGroup (Fin 4)
abbrev Coord := (Fin 3 × Fin 3) × Fin 12

def involution : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩
def threeCycle : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩
def generators : Fin 4 → Source :=
  ![(Multiplicative.ofAdd (1, 0), 1), (Multiplicative.ofAdd (0, 1), 1),
    (1, involution), (1, threeCycle)]
def a4Words : Fin 12 → List (Fin 4) :=
  ![[], [2], [3], [2, 3], [3, 2], [3, 3], [2, 3, 2], [2, 3, 3], [3, 2, 3], [3, 3, 2], [3, 2, 3, 3], [3, 3, 2, 3]]
def words (c : Coord) : List (Fin 4) :=
  List.replicate c.1.1.val 0 ++ List.replicate c.1.2.val 1 ++ a4Words c.2

def e9Form (c : Fin 3 × Fin 3) : Multiplicative (ZMod 3 × ZMod 3) :=
  Multiplicative.ofAdd ((c.1.val : ZMod 3), (c.2.val : ZMod 3))
def a4Form (k : Fin 12) : alternatingGroup (Fin 4) :=
  (evalWord generators (a4Words k)).2
def sourceForm (c : Coord) : Source := (e9Form c.1, a4Form c.2)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem e9Form_bijective : Function.Bijective e9Form := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem a4Form_bijective : Function.Bijective a4Form := by decide +kernel
noncomputable def sourceEquiv : Coord ≃ Source :=
  Equiv.prodCongr (Equiv.ofBijective e9Form e9Form_bijective)
    (Equiv.ofBijective a4Form a4Form_bijective)

theorem sourceEquiv_apply (c : Coord) : sourceEquiv c = sourceForm c := rfl
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem words_spec : ∀ c, evalWord generators (words c) = sourceForm c := by decide +kernel

def a4Next : Fin 12 → Fin 2 → Fin 12 :=
  ![![1, 2], ![0, 3], ![4, 5], ![6, 7], ![2, 8], ![9, 0], ![3, 9], ![8, 1], ![7, 10], ![5, 11], ![11, 4], ![10, 6]]
def next (c : Coord) (i : Fin 4) : Coord :=
  ![((c.1.1 + 1, c.1.2), c.2), ((c.1.1, c.1.2 + 1), c.2),
    (c.1, a4Next c.2 0), (c.1, a4Next c.2 1)] i
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem next_spec : ∀ c i, sourceForm (next c i) = sourceForm c * generators i := by decide +kernel

variable {G : Type*} [Group G]

def normalForm (g : Fin 4 → G) (c : Coord) : G := evalWord g (words c)

noncomputable def candidate (g : Fin 4 → G) (s : Source) : G :=
  normalForm g (sourceEquiv.symm s)

theorem candidate_sourceForm (g : Fin 4 → G) (c : Coord) :
    candidate g (sourceForm c) = normalForm g c := by
  change normalForm g (sourceEquiv.symm (sourceEquiv c)) = _
  rw [sourceEquiv.symm_apply_apply]

theorem candidate_one (g : Fin 4 → G) : candidate g 1 = 1 := by
  have h : sourceForm ((0, 0), 0) = 1 := rfl
  rw [← h, candidate_sourceForm]
  rfl

theorem candidate_mul (g : Fin 4 → G)
    (hnext : ∀ c i, normalForm g (next c i) = normalForm g c * g i)
    (s t : Source) : candidate g (s * t) = candidate g s * candidate g t := by
  have step (s : Source) (i : Fin 4) :
      candidate g (s * generators i) = candidate g s * g i := by
    obtain ⟨c, rfl⟩ := sourceEquiv.surjective s
    rw [sourceEquiv_apply, ← next_spec, candidate_sourceForm, candidate_sourceForm]
    exact hnext c i
  have path (w : List (Fin 4)) : ∀ s : Source,
      candidate g (s * evalWord generators w) = candidate g s * evalWord g w := by
    induction w with
    | nil => intro s; simp [evalWord]
    | cons i w ih =>
      intro s
      rw [evalWord, ← mul_assoc, ih, step, mul_assoc, evalWord]
  obtain ⟨c, rfl⟩ := sourceEquiv.surjective t
  rw [sourceEquiv_apply, ← words_spec c, path]
  rw [words_spec c, candidate_sourceForm]
  rfl

/-- A finite right-generator table supplies all multiplication identities. -/
noncomputable def homOfTransitions (g : Fin 4 → G)
    (hnext : ∀ c i, normalForm g (next c i) = normalForm g c * g i) : Source →* G where
  toFun := candidate g
  map_one' := candidate_one g
  map_mul' := candidate_mul g hnext

/-- Separation of the 108 normal forms makes the constructed homomorphism faithful. -/
theorem homOfTransitions_injective (g : Fin 4 → G)
    (hnext : ∀ c i, normalForm g (next c i) = normalForm g c * g i)
    (hinj : Function.Injective (normalForm g)) : Function.Injective (homOfTransitions g hnext) :=
  hinj.comp sourceEquiv.symm.injective

end Theory.SpecificGroups.E9A4
