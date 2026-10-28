module
public import Theory.GroupTheory.CosetWordCertificate.Tietze
public import Theory.GroupTheory.CosetWordCertificate.Schreier

/-!
# Word identities for the natural-point presentation reduction

Cyclic conjugation, inversion, substitution by an established generator
equation, and products of relations justify the concrete replay in `Checked`.
The computation only compares words; the semantics hold in every group.
Source: elementary Tietze transformations; see `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G]

def variant (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  (if inv then FreeGroup.invRev w else w).rotate offset

def normalize (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  reduce (variant (reduce w) inv offset)

theorem eval_rotate (g : Nat → G) (w : Word Nat) (n : Nat)
    (h : eval g w = 1) : eval g (w.rotate n) = 1 := by
  simpa [eval, FreeGroup.lift_mk, List.map_rotate] using
    List.prod_rotate_eq_one_of_prod_eq_one
      (by simpa [eval, FreeGroup.lift_mk] using h) n

theorem variant_relation (g : Nat → G) (w : Word Nat) (inv : Bool) (offset : Nat)
    (h : eval g w = 1) : eval g (variant w inv offset) = 1 := by
  apply eval_rotate
  cases inv <;> simp [h, eval_invRev]

theorem normalized_relation (g : Nat → G) (w v : Word Nat) (inv : Bool) (offset : Nat)
    (check : normalize w inv offset = v) (h : eval g w = 1) : eval g v = 1 := by
  rw [← check, normalize, eval_reduce]
  exact variant_relation g _ inv offset (by rwa [eval_reduce])

theorem substitution_relation (g : Nat → G) (x : Nat) (u w v : Word Nat)
    (inv : Bool) (offset : Nat) (check : normalize (substitute x u w) inv offset = v)
    (hx : g x = eval g u) (hw : eval g w = 1) : eval g v = 1 :=
  normalized_relation g _ v inv offset check ((eval_substitute g x u w hx).trans hw)

theorem rewrite_relation (g : Nat → G) (w u v : Word Nat)
    (uinv : Bool) (uoff woff : Nat) (inv : Bool) (offset : Nat)
    (check : normalize (FreeGroup.invRev (variant u uinv uoff) ++ w.rotate woff)
      inv offset = v) (hw : eval g w = 1) (hu : eval g u = 1) : eval g v = 1 := by
  apply normalized_relation g _ v inv offset check
  rw [eval_append, eval_invRev, variant_relation g u uinv uoff hu, eval_rotate g w woff hw]
  simp

theorem generator_equation (g : Nat → G) (x : Nat) (v w : Word Nat)
    (inv : Bool) (offset : Nat)
    (check : normalize w inv offset = [(x, true)] ++ FreeGroup.invRev v)
    (hw : eval g w = 1) : g x = eval g v :=
  eq_of_eval_relation g x v (normalized_relation g w _ inv offset check hw)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.NativeActions.Presentation.OrderBound.CosetCover.PointSchreier.PointBound.Reduction
