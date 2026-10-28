module

public import Theory.GroupTheory.CosetEnumeration
public import Theory.GroupTheory.CosetWordCertificate

/-!
# Elementary rules for the Held M₁ Tietze transfer

A relator is an actual word whose value is one in an arbitrary group. The
rules below preserve this interpretation through free reduction, cyclic
rotation, inversion, multiplication, and substitution by a proved generator
equation. The normalization equivalence supports replay in either direction.
Generator recovery uses closure in an arbitrary subgroup, with no normality
assumption and without killing the three protected generators.

These are the elementary group identities needed to certify the retained
Tietze trace for John Bray's ATLAS presentation `Held/Model/Source/HeG1-P1.M`.
They do not themselves assert that the 49 selected relations follow from the
Schreier inputs; the concrete proof DAG must supply that connection.
-/

@[expose] public section

open Theory.GroupTheory.CosetEnumeration
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer

variable {G : Type*} [Group G] (g : Nat → G)

-- Both word APIs have exactly the same semantics.
theorem eval_eq_free (w : Word Nat) :
    eval g w = Subgroup.CosetWordCertificate.eval g w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [show eval g (a :: w) = letterValue g a * eval g w by simp [eval]]
    rw [Subgroup.CosetWordCertificate.eval_cons, ih]
    rfl

theorem eval_reduce (w : Word Nat) :
    eval g (Subgroup.CosetWordCertificate.reduce w) = eval g w := by
  simpa only [eval_eq_free] using Subgroup.CosetWordCertificate.eval_reduce g w

-- A single checked normalization, allowing inversion and cyclic rotation.
def normalize (w : Word Nat) (inv : Bool) (offset : Nat) : Word Nat :=
  Subgroup.CosetWordCertificate.reduce
    (variant (Subgroup.CosetWordCertificate.reduce w) inv offset)

theorem normalize_sound (w : Word Nat) (h : eval g w = 1)
    (inv : Bool) (offset : Nat) : eval g (normalize w inv offset) = 1 := by
  rw [normalize, eval_reduce]
  exact eval_variant g _ (by rw [eval_reduce]; exact h) inv offset

theorem eval_rotate_iff (w : Word Nat) (n : Nat) :
    eval g (w.rotate n) = 1 ↔ eval g w = 1 := by
  rw [List.rotate_eq_drop_append_take_mod, eval_append]
  conv_rhs => rw [← List.take_append_drop (n % w.length) w, eval_append]
  exact mul_eq_one_comm

theorem normalize_iff (w : Word Nat) (inv : Bool) (offset : Nat) :
    eval g (normalize w inv offset) = 1 ↔ eval g w = 1 := by
  rw [normalize, eval_reduce, variant, eval_rotate_iff]
  cases inv <;> simp [eval_reduce]

theorem relation_of_normalize {w v : Word Nat} (inv : Bool) (offset : Nat)
    (check : normalize w inv offset = v) (hw : eval g w = 1) :
    eval g v = 1 := by
  rw [← check]
  exact normalize_sound g w hw inv offset

theorem relation_of_denormalize {w v : Word Nat} (inv : Bool) (offset : Nat)
    (check : normalize w inv offset = v) (hv : eval g v = 1) :
    eval g w = 1 := (normalize_iff g w inv offset).mp (check.symm ▸ hv)

theorem relation_product {u v : Word Nat} (hu : eval g u = 1)
    (hv : eval g v = 1) : eval g (u ++ v) = 1 := by rw [eval_append, hu, hv, one_mul]

theorem equality_of_relation (u v : Word Nat)
    (h : eval g (u ++ inverse v) = 1) : eval g u = eval g v := by
  simpa only [eval_append, eval_inverse, mul_inv_eq_one] using h

theorem relation_of_equality (u v : Word Nat)
    (h : eval g u = eval g v) : eval g (u ++ inverse v) = 1 := by
  simp only [eval_append, eval_inverse, h, mul_inv_cancel]

theorem eval_congr_append {u u' v v' : Word Nat}
    (hu : eval g u = eval g u') (hv : eval g v = eval g v') :
    eval g (u ++ v) = eval g (u' ++ v') := by rw [eval_append, eval_append, hu, hv]

theorem eval_congr_inverse {u v : Word Nat} (h : eval g u = eval g v) :
    eval g (inverse u) = eval g (inverse v) := by simp only [eval_inverse, h]

-- Substitute a word for a generator, retaining inverse letters.
def substitute (a : Nat) (v : Word Nat) (w : Word Nat) : Word Nat :=
  w.flatMap fun b => if b.1 = a then if b.2 then v else inverse v else [b]

theorem substitute_sound (a : Nat) (v w : Word Nat)
    (ha : g a = eval g v) : eval g (substitute a v w) = eval g w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [substitute, List.flatMap_cons, eval_append] at *
    rw [ih]
    congr 1
    split
    · rename_i hb
      rcases b with ⟨b, s⟩
      change b = a at hb
      subst b
      cases s <;> simp [letterValue, ha]
    · simp


theorem eval_mem (H : Subgroup G) (w : Word Nat)
    (hw : ∀ a ∈ w, g a.1 ∈ H) : eval g w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons a w ih =>
    rw [show eval g (a :: w) = letterValue g a * eval g w by simp [eval]]
    refine H.mul_mem ?_ (ih (fun b hb => hw b (List.mem_cons_of_mem a hb)))
    have ha := hw a (List.mem_cons_self)
    rcases a with ⟨a, s⟩
    cases s
    · exact H.inv_mem ha
    · exact ha

theorem generator_mem_of_equation (H : Subgroup G) (a : Nat) (w : Word Nat)
    (ha : g a = eval g w) (hw : ∀ b ∈ w, g b.1 ∈ H) : g a ∈ H := by
  rw [ha]
  exact eval_mem g H w hw

-- The zero integer is syntax for an empty word, never the generator g 0.
def signedLetter : Int → Word Nat
  | .ofNat 0 => []
  | .ofNat (n + 1) => [(n + 1, true)]
  | .negSucc n => [(n + 1, false)]

def signedWord (w : List Int) : Word Nat := w.flatMap signedLetter


theorem signed_congr {u v : List Int}
    (h : List.Forall₂ (fun a b => eval g (signedLetter a) = eval g (signedLetter b)) u v) :
    eval g (signedWord u) = eval g (signedWord v) := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    simp only [signedWord, List.flatMap_cons, eval_append] at *
    rw [hab, ih]

theorem generator_eq_of_relation (a : Nat) (w : Word Nat)
    (h : eval g ([(a, true)] ++ inverse w) = 1) : g a = eval g w := by
  simpa only [eval_singleton, letterValue, if_true] using
    equality_of_relation g [(a, true)] w h

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Cosets.TietzeTransfer
