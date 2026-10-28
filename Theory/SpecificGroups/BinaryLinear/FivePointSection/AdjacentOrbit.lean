module
public import Theory.SpecificGroups.BinaryLinear.FivePointSection.KernelOrbit
/-!
# Small orbits for an adjacent binary five-space flag

The two tail rows have the same GL₃(2) action. Once a nonzero second row
is normalized, translating the first row and applying elementary coordinate
changes produce seventeen distinct pairs. The normalization and the short
witness words are checked over the eight binary triples. The consumer
constructs that translation from a commutator in the actual kernel.

Source: the mixed point-section obstruction in Aschbacher--Smith,12.9.6,
printed pp.861--862.
-/
public section
namespace BinaryLinear.FivePointSection.AdjacentOrbit
abbrev Vec := KernelOrbit.Vec
abbrev Pair := KernelOrbit.Pair
@[expose] def act (g : Fin 6) (x : Pair) : Pair :=
  let ij := KernelOrbit.indices g
  (Function.update x.1 ij.2 (x.1 ij.2 + x.1 ij.1),
   Function.update x.2 ij.2 (x.2 ij.2 + x.2 ij.1))
@[expose] def toggle (x : Pair) : Pair := (x.1 + ![1,0,0],x.2)
private def run (w : List (Fin 6)) (x : Pair) : Pair := w.foldl (fun y g => act g y) x
private def code (v : Vec) : ℕ := (v 0).val+2*(v 1).val+4*(v 2).val
private def normalize (v : Vec) : List (Fin 6) :=
 ([[],[],[2,0],[0],[4,1],[1],[2,0,1],[0,1]] : List (List (Fin 6)))[code v]?.getD []
private theorem normalization : ∀ x : Pair, x.2 ≠ 0 →
    (run (normalize x.2) x).2 = ![1,0,0] := by decide +kernel
private theorem run_mem (s : Set Pair) (h : ∀ g x, x ∈ s → act g x ∈ s)
    (w : List (Fin 6)) (x : Pair) (hx : x ∈ s) : run w x ∈ s := by
  induction w generalizing x with
  | nil => exact hx
  | cons g w ih => exact ih (act g x) (h g x hx)

theorem normalized_member (s : Set Pair) (h : ∀ g x, x ∈ s → act g x ∈ s)
    (x : Pair) (hx : x ∈ s) (hv : x.2 ≠ 0) : ∃ y ∈ s, y.2 = ![1,0,0] :=
  ⟨run (normalize x.2) x,run_mem s h _ x hx,normalization x hv⟩

private def step (g : Fin 7) (x : Pair) : Pair :=
  if h : g.val < 6 then act ⟨g.val,h⟩ x else toggle x
private def runAll (w : List (Fin 7)) (x : Pair) : Pair := w.foldl (fun y g => step g y) x
private def witnesses (u : Vec) (i : Fin 17) : List (Fin 7) :=
  let ws := ([[[],[0],[1],[6],[0,1],[0,2],[0,6],[1,4],[1,6],[6,0],[6,1],[0,1,2],[0,1,6],[0,2,6],[0,6,0],[0,6,1],[1,4,6]],[[],[0],[1],[6],[0,1],[0,2],[0,6],[1,4],[1,6],[6,0],[6,1],[0,1,2],[0,1,6],[0,2,6],[0,6,0],[0,6,1],[1,4,6]],[[],[0],[1],[2],[3],[0,1],[0,2],[0,3],[0,6],[1,2],[1,3],[1,4],[2,0],[2,1],[2,3],[3,0],[3,5]],[[],[0],[1],[2],[3],[0,1],[0,2],[0,3],[0,6],[1,2],[1,3],[1,4],[2,0],[2,1],[2,3],[3,0],[3,5]],[[],[0],[1],[4],[5],[0,1],[0,2],[0,4],[0,5],[1,4],[1,5],[1,6],[4,0],[4,1],[4,5],[5,1],[5,3]],[[],[0],[1],[4],[5],[0,1],[0,2],[0,4],[0,5],[1,4],[1,5],[1,6],[4,0],[4,1],[4,5],[5,1],[5,3]],[[],[0],[1],[2],[3],[5],[0,1],[0,2],[0,3],[0,4],[0,5],[1,2],[1,3],[1,4],[1,5],[2,0],[2,1]],[[],[0],[1],[2],[3],[5],[0,1],[0,2],[0,3],[0,4],[0,5],[1,2],[1,3],[1,4],[1,5],[2,0],[2,1]] ] : List (List (List (Fin 7))))[code u]?.getD []
  ws[i.val]?.getD []
private theorem witnesses_injective : ∀ u : Vec,
    Function.Injective (fun i : Fin 17 => runAll (witnesses u i) (u,![1,0,0])) := by decide +kernel
private theorem runAll_mem (s : Set Pair) (h : ∀ g x, x ∈ s → act g x ∈ s)
    (ht : ∀ x ∈ s, toggle x ∈ s) (w : List (Fin 7)) (x : Pair) (hx : x ∈ s) :
    runAll w x ∈ s := by
  induction w generalizing x with
  | nil => exact hx
  | cons g w ih =>
    apply ih (step g x)
    unfold step
    split
    · exact h _ _ hx
    · exact ht _ hx

theorem large_image {A : Type*} [Finite A] (f : A → Pair)
    (h : ∀ g x, x ∈ Set.range f → act g x ∈ Set.range f)
    (ht : ∀ x ∈ Set.range f, toggle x ∈ Set.range f)
    (x : A) (hv : (f x).2 = ![1,0,0]) : 17 ≤ Nat.card A := by
  classical
  have hr : ((f x).1,![1,0,0]) ∈ Set.range f := ⟨x,by rw [←hv]⟩
  have hw (i : Fin 17) : ∃ y, f y = runAll (witnesses (f x).1 i) ((f x).1,![1,0,0]) :=
    runAll_mem _ h ht _ _ hr
  let t : Fin 17 → A := fun i => (hw i).choose
  have hi : Function.Injective t := by
    intro i j he
    apply witnesses_injective (f x).1
    exact (hw i).choose_spec.symm.trans ((congrArg f he).trans (hw j).choose_spec)
  simpa using Nat.card_le_card_of_injective t hi
end BinaryLinear.FivePointSection.AdjacentOrbit
