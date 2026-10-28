module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.IntrinsicStructure
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Tactic.FinCases

/-!
# Perfection and the square-root orbit of the literal J₂ centralizer

Two short commutator identities put both generators of the literal centralizer
`Seed.l₁` in its derived subgroup, proving perfection. In the existing 32-element
radical enumeration, entry 15 is `Seed.z` and entry 4 squares to it. Short words
in the centralizer generators conjugate entry 4 to each of the twenty square
roots. A check at point 1 excludes the other twelve entries; the conjugation
identities are checked on every point of the faithful degree-100 action.

The established five-point action identifies this radical with `pCore 2 l₁`.
Thus both existence and conjugacy are intrinsic to the literal subgroup of
`Sporadic.LeechRelated.J2.Carrier`, without any assumption from its extension
shape. The finite calculations use the kernel and reuse the existing radical
and centralizer tables. No new carrier enumeration is required.

Source: Aschbacher–Smith, I.2.2 proof, printed pp.411–412 / PDF pp.422–423,
combined manuscript of 1 March 2004. ATLAS J2G1-p100B0 attribution and license
are retained in `AtlasCarriers/source/`; the original CFSG witness search in
`CoverSquareOrbit/source/discover.py` is Apache 2.0 and is not trusted by Lean.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Sporadic.LeechRelated.J2
open GeneratorPair FirstFusion
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.FirstParabolic

namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit

private def localValue : List (Fin 3) → Fin 100 → Fin 100
  | [], p => p
  | s :: w, p => LocalCertificate.localLetterValue s (localValue w p)

private theorem localValue_spec (w : List (Fin 3)) (p : Fin 100) :
    localValue w p = inclusion (evalWord centralizerLetter w) p := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    simp only [localValue, ih, LocalCertificate.localLetterValue_eq,
      evalWord, map_mul, Equiv.Perm.mul_apply]

private def commLeft : Fin 2 → List (Fin 3) := ![[2, 2, 0, 1], [2, 0, 2]]
private def commRight : Fin 2 → List (Fin 3) := ![[1, 0, 2, 2, 0], [0, 1, 0, 2, 0, 1, 0]]

set_option maxRecDepth 100000 in
private theorem comm_check : ∀ (i : Fin 2) (p : Fin 100),
    localValue (commLeft i) (localValue (commRight i) p) =
      LocalCertificate.localLetterValue i.castSucc
        (localValue (commRight i) (localValue (commLeft i) p)) := by
  decide +kernel

private theorem local_mem (w : List (Fin 3)) : evalWord centralizerLetter w ∈ l₁ := by
  induction w with
  | nil => exact l₁.one_mem
  | cons i w ih => exact l₁.mul_mem (centralizerLetter_mem i) ih

private theorem generator_comm (i : Fin 2) :
    ⁅evalWord centralizerLetter (commLeft i), evalWord centralizerLetter (commRight i)⁆ =
      centralizerLetter i.castSucc := by
  have h : evalWord centralizerLetter (commLeft i) * evalWord centralizerLetter (commRight i) =
      centralizerLetter i.castSucc * evalWord centralizerLetter (commRight i) *
        evalWord centralizerLetter (commLeft i) := by
    apply Sporadic.LeechRelated.J2.inclusion_injective
    apply Equiv.ext
    intro p
    simp only [map_mul, Equiv.Perm.mul_apply]
    simpa only [localValue_spec, LocalCertificate.localLetterValue_eq] using comm_check i p
  rw [commutatorElement_def, h]
  group

private theorem generator_mem (i : Fin 2) : centralizerLetter i.castSucc ∈ ⁅l₁, l₁⁆ := by
  rw [← generator_comm i]
  exact commutator_mem_commutator (local_mem _) (local_mem _)

/-- The literal central involution centralizer is perfect. -/
theorem l₁_isPerfect : Group.IsPerfect l₁ := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm
  · simpa using commutator_le_sup l₁ l₁
  · change centralizer ≤ ⁅l₁, l₁⁆
    rw [LocalCertificate.centralizer_eq_closure_letters]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact generator_mem 0
    · exact generator_mem 1
    · exact (⁅l₁, l₁⁆).inv_mem (generator_mem 1)


/-- The literal marked involution of the centralizer. -/
@[expose] def tL : l₁ := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩

private def radicalLift (i : Fin 32) : l₁ :=
  ⟨radicalElement i, radical_le_l₁ (radicalElement_mem i)⟩

private theorem radicalLift_mem_core (i : Fin 32) : radicalLift i ∈ pCore 2 l₁ := by
  rw [l₁_core_eq]
  exact radicalElement_mem i

set_option maxRecDepth 100000 in
private theorem marked_check : ∀ p : Fin 100,
    RadicalStructureData.tablePerm 15 p = tPerm p := by
  decide +kernel

private theorem radicalElement_marked : radicalElement 15 = z := by
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [radicalElement_inclusion]
  change RadicalStructureData.tablePerm 15 = inclusion t
  rw [inclusion_t]
  exact Equiv.ext marked_check

set_option maxRecDepth 100000 in
private theorem square_check : ∀ p : Fin 100,
    RadicalStructureData.tablePerm 4 (RadicalStructureData.tablePerm 4 p) =
      RadicalStructureData.tablePerm 15 p := by
  decide +kernel

private theorem root_square : radicalLift 4 ^ 2 = tL := by
  apply Subtype.ext
  change radicalElement 4 ^ 2 = z
  rw [← radicalElement_marked]
  apply Sporadic.LeechRelated.J2.inclusion_injective
  rw [map_pow, radicalElement_inclusion, radicalElement_inclusion, pow_two]
  exact Equiv.ext square_check

private def conjugatorWord (i : Fin 32) : List (Fin 3) :=
  match i.val with
  | 4 => []
  | 5 => [0, 1]
  | 6 => [2, 0]
  | 8 => [2, 0, 2, 0]
  | 9 => [2]
  | 10 => [1]
  | 11 => [0, 2, 0]
  | 12 => [2, 0, 1, 0, 2, 0]
  | 13 => [1, 1, 0]
  | 17 => [1, 0]
  | 18 => [0, 2, 0, 1, 1, 0]
  | 20 => [2, 0, 1, 1, 0]
  | 21 => [0]
  | 22 => [0, 1, 0, 2, 0]
  | 24 => [1, 1]
  | 26 => [1, 0, 2, 0]
  | 28 => [0, 2, 0, 2, 0]
  | 29 => [0, 2]
  | 30 => [0, 1, 1, 0]
  | 31 => [1, 0, 2, 0, 1, 1, 0]
  | _ => []

-- Equality at point 1 excludes all twelve nonsquare entries before checking
-- the twenty positive conjugation identities on the full 100-point action.
set_option maxRecDepth 100000 in
private theorem conjugator_check : ∀ (i : Fin 32) (p : Fin 100),
    RadicalStructureData.tablePerm i (RadicalStructureData.tablePerm i 1) =
        RadicalStructureData.tablePerm 15 1 →
      localValue (conjugatorWord i) (RadicalStructureData.tablePerm 4 p) =
        RadicalStructureData.tablePerm i (localValue (conjugatorWord i) p) := by
  decide +kernel

private theorem root_isConj (i : Fin 32) (hi : radicalLift i ^ 2 = tL) :
    IsConj (radicalLift 4) (radicalLift i) := by
  have hs : RadicalStructureData.tablePerm i (RadicalStructureData.tablePerm i 1) =
      RadicalStructureData.tablePerm 15 1 := by
    have h : radicalElement i ^ 2 = radicalElement 15 :=
      (congrArg Subtype.val hi).trans radicalElement_marked.symm
    have hv := congrArg (fun x : Carrier => inclusion x 1) h
    simpa only [map_pow, pow_two, map_mul, Equiv.Perm.mul_apply,
      radicalElement_inclusion] using hv
  let g : l₁ := ⟨evalWord centralizerLetter (conjugatorWord i), local_mem _⟩
  apply isConj_iff.mpr
  refine ⟨g, mul_inv_eq_iff_eq_mul.mpr ?_⟩
  apply Subtype.ext
  apply Sporadic.LeechRelated.J2.inclusion_injective
  change inclusion (evalWord centralizerLetter (conjugatorWord i) * radicalElement 4) =
    inclusion (radicalElement i * evalWord centralizerLetter (conjugatorWord i))
  apply Equiv.ext
  intro p
  simpa only [map_mul, Equiv.Perm.mul_apply, radicalElement_inclusion, localValue_spec]
    using conjugator_check i p hs

/-- A square root of the distinguished involution lies in the actual two-core. -/
theorem exists_core_square : ∃ r ∈ pCore 2 l₁, r ^ 2 = tL :=
  ⟨radicalLift 4, radicalLift_mem_core 4, root_square⟩

/-- All two-core square roots are conjugate inside the literal centralizer. -/
theorem core_square_isConj (r : l₁) (hr : r ∈ pCore 2 l₁)
    (s : l₁) (hs : s ∈ pCore 2 l₁) (hr2 : r ^ 2 = tL) (hs2 : s ^ 2 = tL) :
    IsConj r s := by
  rw [l₁_core_eq] at hr hs
  obtain ⟨i, hi⟩ := exists_radicalElement hr
  obtain ⟨j, hj⟩ := exists_radicalElement hs
  have hir : radicalLift i = r := Subtype.ext hi
  have hjs : radicalLift j = s := Subtype.ext hj
  subst r
  subst s
  exact (root_isConj i hr2).symm.trans (root_isConj j hs2)

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
