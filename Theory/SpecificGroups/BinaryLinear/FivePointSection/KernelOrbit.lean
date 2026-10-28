module
public import Theory.SpecificGroups.BinaryLinear.FivePointSection
/-!
# Small conjugation orbits of a binary row and column

Elementary changes of three coordinates act contragrediently on a row and a
column. If both are nonzero, their orbit contains seventeen distinct pairs.
A short normalization word reduces to the incident and nonincident standard
pairs; seventeen explicit words then give the required injection. The finite
certificates check only these words, without enumerating a matrix group or
constructing an orbit closure in the kernel.

This is the order-sixteen kernel calculation for the transvection flag in
Aschbacher--Smith,12.9.6, printed pp.861--862. The actual conjugation action
and application to the source quotient are supplied by the consumer.
-/

public section
namespace BinaryLinear.FivePointSection.KernelOrbit
abbrev Vec := Fin 3 → ZMod 2
abbrev Pair := Vec × Vec

@[expose] def indices (g : Fin 6) : Fin 3 × Fin 3 := ![(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)] g

@[expose] def act (g : Fin 6) (x : Pair) : Pair :=
  let ij := indices g
  (Function.update x.1 ij.2 (x.1 ij.2 + x.1 ij.1),
   Function.update x.2 ij.1 (x.2 ij.1 + x.2 ij.2))

private def run (w : List (Fin 6)) (x : Pair) : Pair := w.foldl (fun y g => act g y) x

private def code (x : Vec) : ℕ := (x 0).val + 2*(x 1).val + 4*(x 2).val

private def normalize (x : Pair) : List (Fin 6) :=
  ([[],[],[],[],[],[],[],[],[],[],[2,0],[0],[2,0,4,1],[1],[2,0,1],[0,1],[],[],[0,2,0],[0,2],[4,1],[1],[0,2,0,1],[0,1,2],[],[2],[2,0],[0],[0,4,1],[1,2],[2,0,1],[0,1],[],[3,5],[1,2,0,5],[0,3,5],[1,4,1],[1,4],[1,4,0,1],[0,1,4],[],[4],[2,0,5],[0,4],[4,1],[1,3,5],[4,0,1],[3,0,5],[],[5],[0,2,0,4],[0,2,4],[0,2,4,1],[1,2,4],[2,5,1],[5,1],[],[2,4],[2,0,4],[0,5],[2,4,1],[1,5],[4,0,1],[3,0,4]] : List (List (Fin 6)))[code x.1 + 8*code x.2]?.getD []

private def representative (b : Bool) : Pair :=
  (![1,0,0], if b then ![1,0,0] else ![0,1,0])

private theorem normalization : ∀ x : Pair, x.1 ≠ 0 → x.2 ≠ 0 →
    ∃ b : Bool, run (normalize x) x = representative b := by
  decide +kernel

private def witnesses (b : Bool) (i : Fin 17) : List (Fin 6) :=
  if b then ![[],[0],[1],[2],[4],[0,1],[0,2],[0,4],[1,2],[1,4],[2,0],[2,4],[4,1],[0,1,2],[0,1,4],[0,2,0],[0,2,4]] i else ![[],[0],[1],[5],[0,1],[0,2],[0,4],[1,4],[1,5],[5,1],[5,3],[0,1,2],[0,1,4],[0,2,4],[0,4,3],[1,4,0],[1,4,5]] i

private theorem witnesses_injective (b : Bool) :
    Function.Injective (fun i : Fin 17 => run (witnesses b i) (representative b)) := by
  revert b
  decide +kernel

private theorem run_mem (s : Set Pair) (h : ∀ g x, x ∈ s → act g x ∈ s)
    (w : List (Fin 6)) (x : Pair) (hx : x ∈ s) : run w x ∈ s := by
  induction w generalizing x with
  | nil => exact hx
  | cons g w ih => exact ih (act g x) (h g x hx)

theorem large_image {A : Type*} [Finite A] (f : A → Pair)
    (h : ∀ g x, x ∈ Set.range f → act g x ∈ Set.range f)
    (x : A) (ha : (f x).1 ≠ 0) (hb : (f x).2 ≠ 0) : 17 ≤ Nat.card A := by
  classical
  obtain ⟨b,he⟩ := normalization (f x) ha hb
  have hr : representative b ∈ Set.range f := he ▸ run_mem _ h _ _ ⟨x,rfl⟩
  have hw (i : Fin 17) : ∃ y, f y = run (witnesses b i) (representative b) :=
    run_mem _ h _ _ hr
  let t : Fin 17 → A := fun i => (hw i).choose
  have ht : Function.Injective t := by
    intro i j hij
    apply witnesses_injective b
    exact (hw i).choose_spec.symm.trans ((congrArg f hij).trans (hw j).choose_spec)
  simpa using Nat.card_le_card_of_injective t ht
end BinaryLinear.FivePointSection.KernelOrbit
