module
public import Theory.SpecificGroups.Rudvalis.Model.MarkedStabilizer.Centralizer.Checks
/-!
# Faithful conjugation on the embedded Tits subgroup

A permutation fixing0 and centralizing the ten original Parrott images fixes
1 and6, using the two checked triples of point-stabilizer words. Commutation
then propagates along the checked orbit tree, so every letter is fixed.
This proves triviality of the Tits centralizer in the actual point stabilizer;
it uses no identification or order assertion about that stabilizer.

Source: the full ²F₄(2) stabilizer in GLS3 Table5.3r, used in J.5.1.
-/
public section
namespace Rudvalis.MarkedStabilizer
open OuterStabilizer.TitsEmbedding
open OuterStabilizer.TitsEmbedding.RelationCertificate
open CentralizerCertificate Theory.GroupTheory

private theorem commute_letter (p : Equiv.Perm (Fin 4060))
    (hp : ∀i, Commute p (permutation i)) (i : Fin 20) :
    Commute p (CentralizerCertificate.letter i) := by
  unfold CentralizerCertificate.letter
  split
  · exact hp _
  · exact (hp _).inv_right

private theorem commute_word (p : Equiv.Perm (Fin 4060))
    (hp : ∀i, Commute p (permutation i)) (w : List (Fin 20)) :
    Commute p (evalWord CentralizerCertificate.letter w) := by
  induction w with
  | nil => exact Commute.one_right p
  | cons i w ih => exact (commute_letter p hp i).mul_right ih

private theorem fix_of_pins (p : Equiv.Perm (Fin 4060)) (h0 : p 0=0)
    (x : Fin 4060) (hx : x≠0) (pin : Fin 3→Equiv.Perm (Fin 4060))
    (hf : ∀j, pin j x=x) (hu : ∀y, (∀j,pin j y=y)→y=0∨y=x)
    (hc : ∀j, Commute p (pin j)) : p x=x := by
  have h := hu (p x) (fun j => by
    have H := Equiv.congr_fun (hc j).eq x
    simpa only [Equiv.Perm.mul_apply,hf] using H.symm)
  exact h.resolve_left (fun h' => hx (p.injective (h'.trans h0.symm)))

/-- The ten literal Tits images have trivial centralizer in the point stabilizer. -/
theorem permutation_eq_one_of_fix_zero_of_commute
    (p : Equiv.Perm (Fin 4060)) (h0 : p 0=0)
    (hp : ∀i, Commute p (permutation i)) : p=1 := by
  have h1 : p 1=1 := fix_of_pins p h0 1 (by decide) pin1 pin1_fix
    (fun x => (checks_all x).2.1) (fun j => commute_word p hp (pins1 j))
  have h6 : p 6=6 := fix_of_pins p h0 6 (by decide) pin6 pin6_fix
    (fun x => (checks_all x).2.2) (fun j => commute_word p hp (pins6 j))
  apply Equiv.ext
  intro x
  change p x=x
  induction x using (measure depth).wf.induction with
  | h x ih =>
    rcases (checks_all x).1 with hx | hx | hx | ⟨hd,he⟩
    · subst x; exact h0
    · subst x; exact h1
    · subst x; exact h6
    · calc
        p x = p (permutation (generator (label x)) (parent x)) := congrArg p he.symm
        _ = permutation (generator (label x)) (p (parent x)) :=
          Equiv.congr_fun (hp (generator (label x))).eq (parent x)
        _ = permutation (generator (label x)) (parent x) := congrArg _ (ih _ hd)
        _ = x := he

/-- The same statement on the original Rudvalis carrier, retaining its action. -/
theorem eq_one_of_fix_zero_of_commute_assignment (g : Model)
    (h0 : g • (0 : Fin 4060)=0) (hp : ∀i, Commute g (assignment i)) : g=1 := by
  apply Subtype.ext
  apply permutation_eq_one_of_fix_zero_of_commute _ h0
  intro i
  rw [permutation_eq]
  exact (hp i).map modelSubgroup.subtype
end Rudvalis.MarkedStabilizer
