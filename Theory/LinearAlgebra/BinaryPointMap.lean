module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Logic.Equiv.Option
public import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FinCases

/-!
# Binary point geometries and their spanning modules

Let a set of point labels span a vector space over `ZMod 2`. Suppose the sum of
the images of any two distinct labels is again a labeled point. If all labeled
vectors are nonzero, the label map is a bijection onto the nonzero vectors:
a collision would make a labeled vector zero, and span induction proves that
no other nonzero vectors occur. For a transitive equivariant map, nonvanishing
follows from the module being nonzero. Faithfulness and dimension then follow.

These are the common linear-algebra steps in Aschbacher–Smith, *The
Classification of Quasithin Groups*, combined manuscript (1 March 2004),
I.5.10 and I.5.15, printed pp. 422–424. The arguments apply to both the
projective and symplectic constructions, independently of their local group
recognition and of the proof that their relation submodules are proper.
-/

namespace Theory.LinearAlgebra.BinaryPointMap
variable {X V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
private theorem add_self (v : V) : v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from rfl, zero_smul]

/-- Distinct labels have distinct images when every distinct pair sums to a nonzero labeled point. -/
public theorem injective (f : X → V) (hne : ∀ x, f x ≠ 0)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z) :
    Function.Injective f := by
  intro x y hxy
  by_contra h
  obtain ⟨z, hz⟩ := hline x y h
  exact hne z (hz.symm.trans (hxy ▸ add_self (f y)))

/-- A spanning family closed under sums of distinct labels contains every nonzero vector. -/
public theorem eq_zero_or_mem_range (f : X → V)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤) (v : V) :
    v = 0 ∨ v ∈ Set.range f := by
  have hv : v ∈ Submodule.span (ZMod 2) (Set.range f) := by rw [hspan]; trivial
  induction hv using Submodule.span_induction with
  | mem v hv => exact Or.inr hv
  | zero => exact Or.inl rfl
  | add v w _ _ hv hw =>
    rcases hv with rfl | ⟨x, rfl⟩
    · simpa using hw
    rcases hw with rfl | ⟨y, rfl⟩
    · exact Or.inr ⟨x, add_zero (f x) |>.symm⟩
    by_cases hxy : x = y
    · subst y; exact Or.inl (add_self (f x))
    · obtain ⟨z, hz⟩ := hline x y hxy
      exact Or.inr ⟨z, hz.symm⟩
  | smul a v _ hv =>
    fin_cases a
    · exact Or.inl (zero_smul (ZMod 2) v)
    · change (1 : ZMod 2) • v = 0 ∨ (1 : ZMod 2) • v ∈ Set.range f
      simpa only [one_smul] using hv

/-- An equivariant spanning family in a nonzero module has no zero image if its labels form one orbit. -/
public theorem nonzero_of_pretransitive {G : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] [DistribMulAction G V] [Nontrivial V]
    (f : X → V) (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤) : ∀ x, f x ≠ 0 := by
  intro x hx
  have hall : ∀ y, f y = 0 := by
    intro y
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G x y
    rw [heq, hx, smul_zero]
  have hbot : Submodule.span (ZMod 2) (Set.range f) = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro v ⟨y, rfl⟩
    exact hall y
  exact top_ne_bot (hspan.symm.trans hbot)

/-- Binary line relations identify the labels with precisely the nonzero vectors. -/
public theorem bijective_nonzero (f : X → V) (hne : ∀ x, f x ≠ 0)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤) :
    Function.Bijective (fun x => (⟨f x, hne x⟩ : {v : V // v ≠ 0})) := by
  constructor
  · intro x y hxy
    exact injective f hne hline (congrArg Subtype.val hxy)
  · intro ⟨v, hv⟩
    obtain hzero | ⟨x, rfl⟩ := eq_zero_or_mem_range f hline hspan v
    · exact (hv hzero).elim
    · exact ⟨x, rfl⟩

/-- A faithful transitive action on binary point labels induces a faithful action on the spanned module. -/
public theorem faithful_of_pretransitive {G : Type*} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X] [DistribMulAction G V] [Nontrivial V]
    [FaithfulSMul G X] (f : X → V)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤) :
    FaithfulSMul G V := by
  let F : X →[G] V := ⟨f, heq⟩
  exact FaithfulSMul.of_injective F
    (injective f (nonzero_of_pretransitive f heq hspan) hline)

/-- A finite binary point geometry with these relations has one fewer point than its vector space. -/
public theorem card [Finite X] (f : X → V) (hne : ∀ x, f x ≠ 0)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤) :
    Nat.card V = Nat.card X + 1 := by
  classical
  let e : X ≃ {v : V // v ≠ 0} := Equiv.ofBijective _ (bijective_nonzero f hne hline hspan)
  let e' : Option X ≃ V := (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe 0)
  rw [← Nat.card_congr e', Finite.card_option]

/-- If the number of labels plus one is `2 ^ n`, the binary vector space has dimension `n`. -/
public theorem finrank [Finite X] (f : X → V) (hne : ∀ x, f x ≠ 0)
    (hline : ∀ x y, x ≠ y → ∃ z, f x + f y = f z)
    (hspan : Submodule.span (ZMod 2) (Set.range f) = ⊤)
    (n : ℕ) (hcard : Nat.card X + 1 = 2 ^ n) :
    Module.finrank (ZMod 2) V = n := by
  classical
  let e : X ≃ {v : V // v ≠ 0} := Equiv.ofBijective _ (bijective_nonzero f hne hline hspan)
  let e' : Option X ≃ V := (Equiv.optionCongr e).trans (Equiv.optionSubtypeNe 0)
  let : Finite V := Finite.of_equiv (Option X) e'
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  calc
    2 ^ Module.finrank (ZMod 2) V = Nat.card V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ = Nat.card X + 1 := card f hne hline hspan
    _ = 2 ^ n := hcard
end Theory.LinearAlgebra.BinaryPointMap
