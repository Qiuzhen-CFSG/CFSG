module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup.AmalgamBound.WordTable

/-!
# Constructing automorphisms from a checked permutation of word coordinates

A permutation that fixes the identity and intertwines multiplication by the
two generators induces an automorphism of the realized group. Word induction
proves the complete multiplication law; a certificate need only check two
translations per row. This is used to construct endpoint extensions in the
binary G₂ amalgam, with the original ATLAS word conventions.
-/

public section
namespace Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound

private theorem map_word_mul {G H : Type*} [Group G] [Group H]
    (f : G → H) (x y : G)
    (hs : ∀ (b : Bool) z, f ((if b then y else x) * z) =
      (if b then f y else f x) * f z) (w : List Bool) (z : G) :
    f (groupWord x y w * z) = groupWord (f x) (f y) w * f z := by
  induction w with
  | nil => simp only [groupWord, one_mul]
  | cons b w ih =>
    simp only [groupWord, mul_assoc, hs, ih]

/-- A checked coordinate permutation supplies a genuine group automorphism. -/
noncomputable def WordTable.Realization.autOfPermutation
    {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (hT : T.Valid) (a : Equiv.Perm (Fin 96))
    (hzero : a 0 = 0)
    (hstep : ∀ (b : Bool) i,
      a (T.mul (if b then 2 else 1) i) =
        T.mul (if b then a 2 else a 1) (a i)) : G ≃* G := by
  let f : G ≃ G := E.equiv.symm.trans (a.trans E.equiv)
  have h1 : f 1 = 1 := by
    change E.equiv (a (E.equiv.symm 1)) = 1
    rw [← E.one_eq, E.equiv.symm_apply_apply, hzero, E.one_eq]
  have hf (i : Fin 96) : f (E.equiv i) = E.equiv (a i) := by
    exact congrArg (fun j => E.equiv (a j)) (E.equiv.symm_apply_apply i)
  have hs (b : Bool) (z : G) :
      f ((if b then E.equiv 2 else E.equiv 1) * z) =
        (if b then f (E.equiv 2) else f (E.equiv 1)) * f z := by
    obtain ⟨i, rfl⟩ := E.equiv.surjective z
    have he := congrArg E.equiv (hstep b i)
    cases b <;>
      simpa only [Bool.false_eq_true, if_false, if_true, ← E.mul_eq, hf] using he
  refine { f with map_mul' := ?_ }
  intro x z
  obtain ⟨i, rfl⟩ := E.equiv.surjective x
  rw [← E.word_eq hT i]
  have h := map_word_mul f (E.equiv 1) (E.equiv 2) hs (T.word i) (1 : G)
  simp only [mul_one, h1] at h
  exact (map_word_mul f (E.equiv 1) (E.equiv 2) hs (T.word i) z).trans
    (congrArg (fun t => t * f z) h.symm)

@[simp] theorem WordTable.Realization.autOfPermutation_apply
    {T : WordTable} {G : Type*} [Group G]
    (E : T.Realization G) (hT : T.Valid) (a : Equiv.Perm (Fin 96))
    (hzero : a 0 = 0)
    (hstep : ∀ (b : Bool) i,
      a (T.mul (if b then 2 else 1) i) =
        T.mul (if b then a 2 else a 1) (a i)) (i : Fin 96) :
    E.autOfPermutation hT a hzero hstep (E.equiv i) = E.equiv (a i) :=
  congrArg (fun j => E.equiv (a j)) (E.equiv.symm_apply_apply i)

end Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
