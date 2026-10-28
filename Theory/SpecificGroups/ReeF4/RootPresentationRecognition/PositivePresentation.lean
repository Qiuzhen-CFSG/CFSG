module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.PositiveTables
public import Mathlib.GroupTheory.PresentedGroup

/-!
# The positive finite root-pair relations and their constructed evaluation

The alphabet consists of eight native relative-root indices with one or two
field parameters. Each relator is a zero root letter or the collected equation
for two root letters, using the fixed native coefficient table. Evaluation in
the full unipotent subgroup is constructed from those equations and is onto.
The twelve-parameter ordered words embed in the abstract group, as witnessed
by their native evaluations. This does not yet prove abstract collection or
injectivity of evaluation on arbitrary words; mixed support and collection
remain necessary for a positive presentation theorem.

Source: GLS3 2.3.7 and 2.4.5, `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.PositivePresentation
open PositiveTables
variable {m : ℕ}

/-- The finite root alphabet, with the actual field parameter spaces. -/
abbrev Letter (m : ℕ) := (i : Root) × Parameter m i

/-- The prescribed eight-factor word in any target group. -/
def word {G : Type*} [Monoid G] (x : (i : Root) → Parameter m i → G)
    (p : Parameters m) : G :=
  (List.ofFn fun i => x (.inl i) (p.1 i)).prod *
    (List.ofFn fun i => x (.inr i) (p.2 i 0,p.2 i 1)).prod

/-- Ordered evaluation commutes with group homomorphisms. -/
theorem map_word {G H : Type*} [Monoid G] [Monoid H] (f : G →* H)
    (x : (i : Root) → Parameter m i → G) (p : Parameters m) :
    f (word x p) = word (fun i a => f (x i a)) p := by
  simp only [word, map_mul, map_list_prod, List.map_ofFn, Function.comp_def]

/-- Literal root letters in the free group. -/
def freeRoot (m : ℕ) (i : Root) (a : Parameter m i) : FreeGroup (Letter m) :=
  FreeGroup.of ⟨i,a⟩

/-- Only zero letters and two-root collected equations are used. -/
inductive Relator (m : ℕ) : FreeGroup (Letter m) → Prop
  | pair_zero (i : Fin 4) : Relator m (freeRoot m (.inl i) 0)
  | quartet_zero (i : Fin 4) : Relator m (freeRoot m (.inr i) (0,0))
  | exchange (i j : Root) (a : Parameter m i) (b : Parameter m j) :
      Relator m (freeRoot m i a * freeRoot m j b *
        (word (freeRoot m) (PositiveTables.exchange i j a b))⁻¹)

/-- This abstract group has not yet been identified with the native unipotent. -/
abbrev Presentation (m : ℕ) := PresentedGroup {w | Relator m w}

/-- The root letters in the abstract group. -/
def generator (m : ℕ) (i : Root) (a : Parameter m i) : Presentation m :=
  PresentedGroup.of ⟨i,a⟩

/-- Finite equations to be checked for a system of root charts. -/
structure Equations {G : Type*} [Group G] (x : (i : Root) → Parameter m i → G) : Prop where
  pair_zero : ∀ i, x (.inl i) 0 = 1
  quartet_zero : ∀ i, x (.inr i) (0,0) = 1
  exchange : ∀ i j a b,
    x i a * x j b = word x (PositiveTables.exchange i j a b)

/-- The defining equations hold in the abstract quotient. -/
theorem generator_equations (m : ℕ) : Equations (generator m) where
  pair_zero i := PresentedGroup.one_of_mem (Relator.pair_zero i)
  quartet_zero i := PresentedGroup.one_of_mem (Relator.quartet_zero i)
  exchange i j a b := by
    apply mul_inv_eq_one.mp
    have h := PresentedGroup.one_of_mem (rels := {w | Relator m w}) (Relator.exchange i j a b)
    rw [map_mul, map_mul, map_inv, map_word] at h
    exact h

theorem Equations.eval_relator {G : Type*} [Group G]
    {x : (i : Root) → Parameter m i → G} (h : Equations x)
    {w : FreeGroup (Letter m)} (hw : Relator m w) :
    FreeGroup.lift (fun a : Letter m => x a.1 a.2) w = 1 := by
  cases hw with
  | pair_zero i => simpa only [freeRoot, FreeGroup.lift_apply_of] using h.pair_zero i
  | quartet_zero i => simpa only [freeRoot, FreeGroup.lift_apply_of] using h.quartet_zero i
  | exchange i j a b =>
    simpa only [map_mul, map_inv, map_word, freeRoot, FreeGroup.lift_apply_of,
      mul_inv_eq_one] using h.exchange i j a b

/-- The equations construct the evaluation; a homomorphism is never an input. -/
def lift {G : Type*} [Group G] {x : (i : Root) → Parameter m i → G}
    (h : Equations x) : Presentation m →* G :=
  PresentedGroup.toGroup (fun _ hw => h.eval_relator hw)

@[simp] theorem lift_generator {G : Type*} [Group G]
    {x : (i : Root) → Parameter m i → G} (h : Equations x) (i : Root) (a : Parameter m i) :
    lift h (generator m i a) = x i a := PresentedGroup.toGroup.of _

/-- Native verification uses the canonical root-pair coefficients. -/
theorem native_equations (m : ℕ) : Equations (PositiveTables.root m) where
  pair_zero := PositiveTables.pair_zero
  quartet_zero := PositiveTables.quartet_zero
  exchange := PositiveTables.exchange_equation

/-- The constructed evaluation lands in the entire actual unipotent of Model m. -/
def nativeEval (m : ℕ) : Presentation m →* Parabolics.unipotent m :=
  lift (native_equations m)

@[simp] theorem nativeEval_generator (i : Root) (a : Parameter m i) :
    nativeEval m (generator m i a) = PositiveTables.root m i a := lift_generator _ i a

/-- The section words evaluate as the literal native twelve-coordinate words. -/
theorem nativeEval_word (p : Parameters m) :
    nativeEval m (word (generator m) p) = PositiveTables.product p := by
  rw [map_word]
  simp only [nativeEval_generator]
  rfl

/-- Every element of the native unipotent has an abstract preimage, for all m. -/
theorem nativeEval_surjective (m : ℕ) : Function.Surjective (nativeEval m) := by
  intro u
  obtain ⟨p, rfl⟩ := (PositiveTables.product_bijective m).surjective u
  exact ⟨word (generator m) p, nativeEval_word p⟩

/-- Distinct ordered coordinate vectors remain distinct in the abstract group. -/
theorem word_injective (m : ℕ) : Function.Injective (word (generator m)) := by
  intro p q hpq
  apply (PositiveTables.product_bijective m).injective
  simpa only [nativeEval_word] using congrArg (nativeEval m) hpq

@[simp] theorem word_zero : word (generator m) (0 : Parameters m) = 1 := by
  simp [word, List.ofFn_succ, (generator_equations m).pair_zero,
    (generator_equations m).quartet_zero]

/-- There is no kernel among the prescribed ordered words. Exhaustion by these
words is the remaining abstract collection obligation. -/
theorem nativeEval_word_eq_one_iff (p : Parameters m) :
    nativeEval m (word (generator m) p) = 1 ↔ p = 0 := by
  rw [nativeEval_word, PositiveTables.product_eq_one_iff]

/-- The two-letter defining relation really produces an ordered word. -/
theorem two_letters_collect (i j : Root) (a : Parameter m i) (b : Parameter m j) :
    generator m i a * generator m j b =
      word (generator m) (PositiveTables.exchange i j a b) :=
  (generator_equations m).exchange i j a b

/-- Concrete binary type V behavior survives in the abstract root relators. -/
theorem binary_suzuki_square :
    generator 0 (.inr 0) (1,0) * generator 0 (.inr 0) (1,0) ≠ 1 := by
  intro he
  have hn := congrArg (nativeEval 0) he
  simp only [map_mul, nativeEval_generator, map_one] at hn
  have hs := congrArg (fun x : Parabolics.unipotent 0 => (x : Model 0)) hn
  simp only [PositiveTables.root, Subgroup.coe_mul, PositiveTables.quartet_simple,
    Subgroup.coe_one] at hs
  exact RootPresentationRecognition.binary_suzuki_square_ne_one true hs

end ReeF4.RootPresentationRecognition.PositivePresentation
