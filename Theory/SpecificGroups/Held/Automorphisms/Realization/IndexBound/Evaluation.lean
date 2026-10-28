module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedSubgroup
public import Theory.SpecificGroups.Held.Automorphisms.Realization.IndexBound.Context
import Mathlib.Tactic.FinCases

/-!
# Realizing Held's coset certificate

The four certificate letters are the standard generators `a,b` and the two
conjugates of `a` defining the marked subgroup. Literal permutation identities
are checked in bounded Boolean blocks, then transported through the faithful
representation. Cyclic rotation of a true relator is justified algebraically.

Source: John Bray's ATLAS `HeG1-P1.M` and the degree-2058 permutation tables.
-/

@[expose] public section
namespace Held.Realization.IndexCertificate
open Subgroup.CosetWordCertificate

/-- The two standard generators, followed by the two marked conjugates. -/
def generator : Fin 4 → He
  | 0 => a
  | 1 => b
  | 2 => markedGenerator 1
  | 3 => markedGenerator 2

def permGenerator (i : Fin 4) : Equiv.Perm (Fin 2058) :=
  representation (generator i)

/-- Executable pointwise evaluation, without constructing free-group quotients. -/
def applyWord : Word (Fin 4) → Fin 2058 → Fin 2058
  | [], x => x
  | (i, s) :: w, x =>
    if s then permGenerator i (applyWord w x)
    else (permGenerator i)⁻¹ (applyWord w x)

theorem applyWord_eq (w : Word (Fin 4)) (x : Fin 2058) :
    applyWord w x = representation (eval generator w) x := by
  induction w with
  | nil => simp [applyWord]
  | cons a w ih =>
    rcases a with ⟨i, s⟩
    cases s <;> simp [applyWord, eval_cons, map_mul, map_inv,
      Equiv.Perm.mul_apply, permGenerator, ih]

/-- Boolean checks avoid building a large finite universal decidability tree. -/
def checkIdentity (w : Word (Fin 4)) (start count : Nat) : Bool :=
  (List.range count).all fun k =>
    let x : Fin 2058 := ⟨(start + k) % 2058, Nat.mod_lt _ (by decide)⟩
    (applyWord w x).val == x.val

theorem checkIdentity_sound (w : Word (Fin 4)) (start count : Nat)
    (h : checkIdentity w start count = true) (k : Nat) (hk : k < count) :
    applyWord w ⟨(start + k) % 2058, Nat.mod_lt _ (by decide)⟩ =
      ⟨(start + k) % 2058, Nat.mod_lt _ (by decide)⟩ := by
  apply Fin.ext
  exact beq_iff_eq.mp (List.all_eq_true.mp h k (List.mem_range.mpr hk))

theorem relator_of_blocks (w : Word (Fin 4))
    (h : ∀ q : Fin 17, checkIdentity w (128 * q.val) 128 = true) :
    eval generator w = 1 := by
  apply representation_injective
  ext x
  rw [map_one, Equiv.Perm.one_apply, ← applyWord_eq]
  have hx := checkIdentity_sound w _ _ (h ⟨x.val / 128, by omega⟩)
    (x.val % 128) (Nat.mod_lt _ (by decide))
  have he : 128 * (x.val / 128) + x.val % 128 = x.val := by omega
  simpa only [he, Nat.mod_eq_of_lt x.isLt] using congrArg Fin.val hx

/-- A cyclic rotation of a relator remains a relator in any group. -/
theorem rotated_relator (u v : Word (Fin 4))
    (h : eval generator (u ++ v) = 1) : eval generator (v ++ u) = 1 := by
  rw [eval_append] at h ⊢
  exact mul_eq_one_comm.mp h

theorem allowed_ok (a : Letter (Fin 4)) (h : context.allowed a = true) :
    eval generator [a] ∈ markedSubgroup := by
  have ha : a = (0, true) ∨ a = (2, true) ∨ a = (3, true) := of_decide_eq_true h
  rcases ha with rfl | rfl | rfl
  · exact markedGenerator_mem 0
  · exact markedGenerator_mem 1
  · exact markedGenerator_mem 2

/-- Enlarging the two standard generators by the marked words preserves generation. -/
theorem generator_closure : Subgroup.closure (Set.range generator) = ⊤ := by
  apply top_unique
  rw [← Held.closure_pair]
  apply Subgroup.closure_mono
  rintro g (rfl | hg)
  · exact ⟨0, rfl⟩
  · obtain rfl := Set.mem_singleton_iff.mp hg
    exact ⟨1, rfl⟩

end Held.Realization.IndexCertificate
