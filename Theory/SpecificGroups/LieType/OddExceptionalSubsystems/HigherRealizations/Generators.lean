module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Folding
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems

/-!
# Marked folded generators in the higher exceptional matrix groups

The first six numbered nodes of E7 and E8 have exactly the E6 Cartan matrix.
We specify the corresponding folded curves, with both signs and in the F4
node order used by `FoldedSubsystem.f4Simple`. These are actual products in
the integral adjoint matrix carriers. Their generated subgroups are defined
without assuming that the assignment from the E6 subgroup respects relations.

Sources: GLS3 §2.6, especially 2.6.2--3 (`refs/KGroup/GLS3/chapter2.tex`),
and Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction

namespace TwistedE6.FoldedSubsystem.HigherRealizations

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

section SignedRoots

variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]
  (F : Type*) [Field F]

/-- The signed simple curve, with the same negative-root convention as E6. -/
def signedSimple (s : Bool) (i : b.support) (t : F) :
    ExceptionalSplit.rootGenerated P b F :=
  let := P.indexNeg
  if s then ExceptionalSplit.elementaryRoot P b F i t
  else ExceptionalSplit.elementaryRoot P b F (-(i : ι)) t

@[simp] theorem signedSimple_val (s : Bool) (i : b.support) (t : F) :
    (signedSimple F s i t).val =
      (RootPairing.SimpleGeckGroup.simpleFamily (b := b)).unit (s, i) t := by
  let := P.indexNeg
  cases s
  · exact rootCurveUnit_neg_simple i t
  · exact rootCurveUnit_simple i t

@[simp] theorem signedSimple_zero (s : Bool) (i : b.support) :
    signedSimple F s i 0 = 1 := by
  apply Subtype.ext
  simp [signedSimple_val]

theorem signedSimple_add (s : Bool) (i : b.support) (t u : F) :
    signedSimple F s i (t + u) = signedSimple F s i t * signedSimple F s i u := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, signedSimple_val]
  exact (RootPairing.SimpleGeckGroup.simpleFamily (b := b)).unit_add _ t u

variable [P.IsIrreducible]

/-- Orthogonal signed simple curves commute, including in characteristic three. -/
theorem signedSimple_commute (s : Bool) (i j : b.support)
    (hij : i ≠ j) (hc : b.cartanMatrix j i = 0) (t u : F) :
    Commute (signedSimple F s i t) (signedSimple F s j u) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, signedSimple_val]
  cases s
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_negative_negative_of_cartan_eq_zero
        i j hij hc t u).eq
  · exact congrArg Subtype.val
      (RootPairing.SimpleGeckGroup.commute_positive_positive_of_cartan_eq_zero
        i j hij hc t u).eq

theorem signedSimple_opposite_commute (i j : b.support)
    (hij : i ≠ j) (t u : F) :
    Commute (signedSimple F true i t) (signedSimple F false j u) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, signedSimple_val]
  exact congrArg Subtype.val
    (RootPairing.SimpleGeckGroup.commute_positive_negative i j hij t u).eq

end SignedRoots

variable (F : Type*) [Field F]

abbrev e7Simple (s : Bool) (i : Fin 7) (t : F) : ExceptionalSplit.e7Cover F :=
  signedSimple F s (typeE7RootPairing_baseEquiv i) t

abbrev e8Simple (s : Bool) (i : Fin 8) (t : F) : ExceptionalSplit.e8Cover F :=
  signedSimple F s (typeE8RootPairing_baseEquiv i) t

/-- The literal simple-node inclusion has the E6 Cartan matrix. -/
theorem e7_cartan_restrict (i j : Fin 6) :
    typeE7CartanMatrix (i.castLE (by decide)) (j.castLE (by decide)) =
      typeE6CartanMatrix i j := by
  fin_cases i <;> fin_cases j <;> decide

theorem e8_cartan_restrict (i j : Fin 6) :
    typeE8CartanMatrix (i.castLE (by decide)) (j.castLE (by decide)) =
      typeE6CartanMatrix i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The four E7 folded curves, numbered as the concrete F4 simple roots. -/
def e7FoldedSimple (s : Bool) (i : Fin 4) (t : F) : ExceptionalSplit.e7Cover F :=
  ![e7Simple F s 3 t, e7Simple F s 2 t,
    e7Simple F s 1 t * e7Simple F s 4 t,
    e7Simple F s 0 t * e7Simple F s 5 t] i

/-- The four E8 folded curves, with exactly the same signed products. -/
def e8FoldedSimple (s : Bool) (i : Fin 4) (t : F) : ExceptionalSplit.e8Cover F :=
  ![e8Simple F s 3 t, e8Simple F s 2 t,
    e8Simple F s 1 t * e8Simple F s 4 t,
    e8Simple F s 0 t * e8Simple F s 5 t] i

def e7FoldedSubgroup : Subgroup (ExceptionalSplit.e7Cover F) :=
  Subgroup.closure (Set.range fun x : Bool × Fin 4 × F =>
    e7FoldedSimple F x.1 x.2.1 x.2.2)

def e8FoldedSubgroup : Subgroup (ExceptionalSplit.e8Cover F) :=
  Subgroup.closure (Set.range fun x : Bool × Fin 4 × F =>
    e8FoldedSimple F x.1 x.2.1 x.2.2)

/-- The E7 properness obligation concerns this literal restricted projection. -/
def e7FoldedProjection : e7FoldedSubgroup F →* ExceptionalSplit.E7 F :=
  (ExceptionalSplit.projection typeE7RootPairing typeE7RootPairing_base F).comp
    (e7FoldedSubgroup F).subtype

theorem e7FoldedSimple_mem (s : Bool) (i : Fin 4) (t : F) :
    e7FoldedSimple F s i t ∈ e7FoldedSubgroup F :=
  Subgroup.subset_closure ⟨(s, i, t), rfl⟩

theorem e8FoldedSimple_mem (s : Bool) (i : Fin 4) (t : F) :
    e8FoldedSimple F s i t ∈ e8FoldedSubgroup F :=
  Subgroup.subset_closure ⟨(s, i, t), rfl⟩

/-- A subgroup of the E6 folded carrier is determined by its marked generators. -/
theorem source_le_of_f4Simple_mem (K : Subgroup (splitSubgroup F))
    (h : ∀ s i t, f4Simple F s i t ∈ K) : ⊤ ≤ K := by
  have hle : splitSubgroup F ≤ K.map (splitSubgroup F).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    refine ⟨f4Simple F s i.rev t, h s i.rev t, ?_⟩
    simp [f4Simple]
  intro x _
  obtain ⟨y, hy, he⟩ := hle x.property
  have : y = x := Subtype.ext he
  exact this ▸ hy

/-- The marked source curves suffice to check that a homomorphism lands in K. -/
theorem range_le_of_f4Simple_mem {G : Type*} [Group G]
    (f : splitSubgroup F →* G) (K : Subgroup G)
    (h : ∀ s i t, f (f4Simple F s i t) ∈ K) : f.range ≤ K := by
  rintro _ ⟨x, rfl⟩
  exact source_le_of_f4Simple_mem F (K.comap f) h (Subgroup.mem_top x)

theorem e7_range_le (f : splitSubgroup F →* ExceptionalSplit.e7Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e7FoldedSimple F s i t) :
    f.range ≤ e7FoldedSubgroup F := by
  apply range_le_of_f4Simple_mem
  intro s i t
  rw [hf]
  exact e7FoldedSimple_mem F s i t

theorem e8_range_le (f : splitSubgroup F →* ExceptionalSplit.e8Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e8FoldedSimple F s i t) :
    f.range ≤ e8FoldedSubgroup F := by
  apply range_le_of_f4Simple_mem
  intro s i t
  rw [hf]
  exact e8FoldedSimple_mem F s i t

theorem e7_range_eq (f : splitSubgroup F →* ExceptionalSplit.e7Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e7FoldedSimple F s i t) :
    f.range = e7FoldedSubgroup F := by
  apply le_antisymm (e7_range_le F f hf)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨s, i, t⟩, rfl⟩
  exact ⟨f4Simple F s i t, hf s i t⟩

theorem e8_range_eq (f : splitSubgroup F →* ExceptionalSplit.e8Cover F)
    (hf : ∀ s i t, f (f4Simple F s i t) = e8FoldedSimple F s i t) :
    f.range = e8FoldedSubgroup F := by
  apply le_antisymm (e8_range_le F f hf)
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨⟨s, i, t⟩, rfl⟩
  exact ⟨f4Simple F s i t, hf s i t⟩

end TwistedE6.FoldedSubsystem.HigherRealizations
