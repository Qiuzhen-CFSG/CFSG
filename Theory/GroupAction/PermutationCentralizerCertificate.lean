module

public import Theory.GroupTheory.WordSubgroup

/-!
# Certificates for the two sporadic Sylow restriction kernels

A commuting permutation preserves the fixed-point pattern of every word in
the generators. Once its images on orbit representatives are known, words
transport those images to every point. The finite certificates use these two
facts to exhaust the restriction kernel, without enumerating automorphisms or
restricting their orders. These facts supply the finite centralizer certificate.

Source: Aschbacher–Smith, combined manuscript, 16.1.6, printed p.1172.
Extracted from the intrinsic certificate in
`CFSG/Quasithin/Chapter16/Section01To02/OtherPreliminaries/JankoTwoHigmanSims/SylowKernels/Certificate.lean`;
the original is preserved. This module has only Theory and Mathlib dependencies.
-/

public section
namespace Theory.GroupAction.PermutationCentralizerCertificate
open Theory.GroupTheory

theorem commute_word {X : Type*} {m : ℕ} (gen : Fin m → Equiv.Perm X)
    (p : Equiv.Perm X) (hp : ∀ i, Commute p (gen i)) (w : List (Fin m)) :
    Commute p (evalWord gen w) := by
  induction w with
  | nil => exact Commute.one_right p
  | cons i w ih => exact (hp i).mul_right ih

theorem fixed_word_iff {X : Type*} {m : ℕ} (gen : Fin m → Equiv.Perm X)
    (p : Equiv.Perm X) (hp : ∀ i, Commute p (gen i)) (w : List (Fin m)) (x : X) :
    evalWord gen w (p x) = p x ↔ evalWord gen w x = x := by
  have he := congrArg (fun q : Equiv.Perm X => q x) (commute_word gen p hp w).eq
  change p (evalWord gen w x) = evalWord gen w (p x) at he
  rw [← he, p.injective.eq_iff]

theorem eq_of_orbit_images {X I : Type*} {m k : ℕ}
    (gen : Fin m → Equiv.Perm X) (base : Fin k → X)
    (orbit : X → Fin k) (word : X → List (Fin m))
    (hword : ∀ x, evalWord gen (word x) (base (orbit x)) = x)
    (candidate : I → Equiv.Perm X) (target : I → Fin k → X)
    (hcandidate : ∀ i x, candidate i x = evalWord gen (word x) (target i (orbit x)))
    (p : Equiv.Perm X) (hp : ∀ j, Commute p (gen j))
    (i : I) (hi : ∀ j, target i j = p (base j)) : p = candidate i := by
  ext x
  rw [hcandidate, hi]
  have he := congrArg (fun q : Equiv.Perm X => q (base (orbit x)))
    (commute_word gen p hp (word x)).eq
  change p (evalWord gen (word x) (base (orbit x))) = _ at he
  simpa only [hword, Equiv.Perm.mul_apply] using he

end Theory.GroupAction.PermutationCentralizerCertificate
