module
public import Theory.GroupTheory.OrderedRootPresentation
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.PositiveRootCharts

/-!
# A finite angular presentation of the full positive Ree subgroup

The native angular commutator calculation proves normalization of later whole
root groups, including at m = 0. It constructs finite conjugation coefficients
on pairs of root parameters. Their local equations imply abstract collection
by `OrderedRootPresentation`; the eight-factor bound agrees with the existing
native twelve-coordinate bijection. Thus the constructed evaluation is an
isomorphism onto the entire native U, without a simplicity or kernel premise.

The alphabet uses the actual root carriers, whose one- and two-field charts and
multiplication laws are proved in PositiveRootCharts. No coefficient is indexed
by arbitrary elements of the full Ree group. These are angular conjugation
relators; source realizations must verify them, and they are not claimed here
to follow from the earlier pair-collection presentation. The signed global
Bruhat presentation and full Ree comparison remain separate obligations.

Source: GLS3 2.4.5(d)--6, `refs/KGroup/GLS3/chapter2.tex`; the positive
collection step of Steinberg, *Lectures on Chevalley Groups*, §11.
-/

@[expose] public noncomputable section
namespace ReeF4.RootPresentationRecognition.AngularPresentation
open Subgroup
open CentralCovers.TwoPrimary CentralCovers.TwoPrimary.TailRelations
open Theory.GroupTheory OrderedRootPresentation

/-- Only the eight native root groups parameterize letters. The field charts
are `PositiveTables.rootChartEquiv`, including the type V cocycle. -/
abbrev Parameter (m : ℕ) (i : PositiveTables.Root) : Type := ElementaryTwoBound.X m (rootIndex i)

def nativeRoot (m : ℕ) (i : PositiveTables.Root) : Parameter m i →* Model m :=
  (ElementaryTwoBound.X m (rootIndex i)).subtype

private theorem native_join (m : ℕ) (l : List PositiveTables.Root) :
    join (Parameter m) (nativeRoot m) l = baseOrderedJoin m l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [join, nativeRoot, Subgroup.range_subtype, baseOrderedJoin, List.foldr_cons, ih]

theorem order_nodup : sourceOrder.Nodup := by decide

private theorem tail_decomposition (i : PositiveTables.Root) :
    ∃ before, sourceOrder = before ++ i :: tail sourceOrder i := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp (mem_sourceOrder i)
  exact ⟨before, by simpa only [tail_eq order_nodup he] using he⟩

private theorem native_normalizes (m : ℕ) (i : PositiveTables.Root) :
    (nativeRoot m i).range ≤ normalizer (join (Parameter m) (nativeRoot m) (tail sourceOrder i)) := by
  obtain ⟨before, he⟩ := tail_decomposition i
  simpa only [nativeRoot, Subgroup.range_subtype, native_join] using
    BaseIntervals.baseNormalizesTails m before i _ he

private theorem native_tail_words (m : ℕ) (i : PositiveTables.Root) (g : Model m)
    (hg : g ∈ join (Parameter m) (nativeRoot m) (tail sourceOrder i)) :
    ∃ a : Tuple (Parameter m) (tail sourceOrder i),
      word (Parameter m) (fun k => nativeRoot m k) (tail sourceOrder i) a = g := by
  apply OrderedRootPresentation.exists_word _ _ _ _ g hg
  intro pre j after he
  obtain ⟨before, hb⟩ := tail_decomposition i
  have hj : sourceOrder = (before ++ i :: pre) ++ j :: after := by
    rw [hb, he]
    simp only [List.append_assoc, List.cons_append]
  simpa only [nativeRoot, Subgroup.range_subtype, native_join] using
    BaseIntervals.baseNormalizesTails m _ j _ hj

theorem conjugate_has_coordinates (m : ℕ) (i j : PositiveTables.Root)
    (hj : j ∈ tail sourceOrder i) (a : Parameter m i) (b : Parameter m j) :
    ∃ p : Tuple (Parameter m) (tail sourceOrder i),
      word (Parameter m) (fun k => nativeRoot m k) (tail sourceOrder i) p =
        (a : Model m) * b * (a : Model m)⁻¹ := by
  apply native_tail_words
  have ha := native_normalizes m i (show nativeRoot m i a ∈ (nativeRoot m i).range from ⟨a,rfl⟩)
  exact (mem_normalizer_iff.mp ha b).mp
    (range_le_join (Parameter m) (nativeRoot m) _ hj ⟨b,rfl⟩)

/-- Fixed native coefficients for conjugating one later root letter by one
earlier root letter. The output is an ordered tail, never a full-group table. -/
def table (m : ℕ) : Table (Parameter m) sourceOrder := by
  exact { conjugate := fun i j hj a b => (conjugate_has_coordinates m i j hj a b).choose }

theorem native_equations (m : ℕ) : Equations (table m) (nativeRoot m) := by
  intro i j hj a b
  exact (conjugate_has_coordinates m i j hj a b).choose_spec.symm

/-- The relations alone give the abstract eight-factor normal form. -/
abbrev Presentation (m : ℕ) := OrderedRootPresentation.Presentation (table m)

instance presentationFinite (m : ℕ) : Finite (Presentation m) :=
  OrderedRootPresentation.finite (table m) order_nodup mem_sourceOrder

theorem normalForm (m : ℕ) (g : Presentation m) :
    ∃ p : Tuple (Parameter m) sourceOrder,
      word (Parameter m) (fun i => root (table m) i) sourceOrder p = g :=
  OrderedRootPresentation.normalForm (table m) order_nodup mem_sourceOrder g

/-- The native root groups generate the entire positive subgroup. -/
theorem native_join_eq (m : ℕ) :
    join (Parameter m) (nativeRoot m) sourceOrder = Parabolics.unipotent m := by
  apply le_antisymm
  · apply join_le
    intro i _
    simpa only [nativeRoot, Subgroup.range_subtype] using ElementaryTwoBound.X_le_unipotent m (rootIndex i)
  · intro u hu
    obtain ⟨p,hp⟩ := blockProduct_surjective m ⟨u,hu⟩
    change blockProduct m p = u at hp
    rw [← hp]
    unfold blockProduct
    apply mul_mem
    all_goals
      apply list_prod_mem
      intro x hx
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact range_le_join (Parameter m) (nativeRoot m) sourceOrder (mem_sourceOrder _) ⟨p _,rfl⟩

theorem nativeEval_range (m : ℕ) :
    (eval (table m) (native_equations m)).range = Parabolics.unipotent m := by
  rw [OrderedRootPresentation.eval_range _ _ order_nodup mem_sourceOrder, native_join_eq]

def nativeEval (m : ℕ) : Presentation m →* Parabolics.unipotent m :=
  (eval (table m) (native_equations m)).codRestrict _ (fun a => by
    rw [← nativeEval_range]
    exact ⟨a,rfl⟩)

@[simp] theorem nativeEval_root (m : ℕ) (i : PositiveTables.Root) (a : Parameter m i) :
    (nativeEval m (root (table m) i a) : Model m) = a := eval_root _ _ i a

theorem nativeEval_surjective (m : ℕ) : Function.Surjective (nativeEval m) := by
  intro u
  have hu : (u : Model m) ∈ (eval (table m) (native_equations m)).range := by
    rw [nativeEval_range]; exact u.property
  obtain ⟨a,ha⟩ := hu
  exact ⟨a,Subtype.ext ha⟩

/-- The abstract coordinate bound is exactly the native twelve-coordinate count. -/
theorem card_tuple (m : ℕ) :
    Nat.card (Tuple (Parameter m) sourceOrder) = Nat.card (Parabolics.unipotent m) := by
  rw [OrderedRootPresentation.card_tuple]
  calc
    _ = Nat.card (Blocks m) := by
      simp only [sourceOrder, List.map_ofFn, List.prod_ofFn, Nat.card_pi]
      exact rootIndexEquiv.symm.prod_comp (fun i => Nat.card (Parameter m i))
    _ = _ := Nat.card_congr (positiveEquiv m)

/-- Both collection and native coordinates, rather than a simplicity or kernel
premise, prove that the constructed native evaluation is faithful. -/
theorem nativeEval_bijective (m : ℕ) : Function.Bijective (nativeEval m) := by
  apply (nativeEval_surjective m).bijective_of_nat_card_le
  rw [← card_tuple m]
  exact OrderedRootPresentation.card_le (table m) order_nodup mem_sourceOrder

def nativeEquiv (m : ℕ) : Presentation m ≃* Parabolics.unipotent m :=
  MulEquiv.ofBijective (nativeEval m) (nativeEval_bijective m)

@[simp] theorem nativeEquiv_root (m : ℕ) (i : PositiveTables.Root) (a : Parameter m i) :
    (nativeEquiv m (root (table m) i a) : Model m) = a := nativeEval_root m i a

end ReeF4.RootPresentationRecognition.AngularPresentation

namespace ReeF4.RootPresentationRecognition.AngularPresentation
open Subgroup Theory.GroupTheory OrderedRootPresentation CentralCovers.TwoPrimary

/-- The angular coordinate map is the literal eight-factor product. -/
def nativeWord (m : ℕ) (p : Tuple (Parameter m) sourceOrder) : Parabolics.unipotent m :=
  ⟨word (Parameter m) (fun i => nativeRoot m i) sourceOrder p, by
    rw [← native_join_eq]
    exact word_mem_join _ _ _ _⟩

theorem nativeWord_surjective (m : ℕ) : Function.Surjective (nativeWord m) := by
  intro u
  obtain ⟨g,hg⟩ := (nativeEval_surjective m) u
  obtain ⟨p,hp⟩ := normalForm m g
  refine ⟨p,?_⟩
  apply Subtype.ext
  exact (OrderedRootPresentation.eval_word (table m) (native_equations m) sourceOrder p).symm.trans
    (by rw [hp]; exact congrArg Subtype.val hg)

theorem nativeWord_bijective (m : ℕ) : Function.Bijective (nativeWord m) :=
  (nativeWord_surjective m).bijective_of_nat_card_le (le_of_eq (card_tuple m))

def nativeCoordinates (m : ℕ) : Tuple (Parameter m) sourceOrder ≃ Parabolics.unipotent m :=
  Equiv.ofBijective _ (nativeWord_bijective m)

/-- Whole angular words are unique in the known matrix model. -/
theorem native_word_injective (m : ℕ) :
    Function.Injective (word (Parameter m) (fun i => nativeRoot m i) sourceOrder) := by
  intro a b he
  exact (nativeWord_bijective m).injective (Subtype.ext he)

/-- A tail word inherits uniqueness by prefixing identity parameters. -/
theorem native_tail_injective (m : ℕ) (i : PositiveTables.Root) :
    Function.Injective (word (Parameter m) (fun k => nativeRoot m k) (tail sourceOrder i)) := by
  obtain ⟨before, after, he⟩ := List.mem_iff_append.mp (mem_sourceOrder i)
  have ht := tail_eq order_nodup he
  apply word_injective_suffix _ _ (before := before ++ [i]) _ (native_word_injective m)
  simpa only [List.append_assoc, List.singleton_append, ht] using he

/-- Each finite conjugation coefficient vector is uniquely specified by its
native equation; the choice in `table` introduces no arbitrary relation. -/
theorem conjugate_unique (m : ℕ) (i j : PositiveTables.Root) (hj : j ∈ tail sourceOrder i)
    (a : Parameter m i) (b : Parameter m j) (p : Tuple (Parameter m) (tail sourceOrder i))
    (hp : (a : Model m)*b*(a : Model m)⁻¹ =
      word (Parameter m) (fun k => nativeRoot m k) (tail sourceOrder i) p) :
    (table m).conjugate i j hj a b = p := by
  apply native_tail_injective
  exact (native_equations m i j hj a b).symm.trans hp

end ReeF4.RootPresentationRecognition.AngularPresentation
