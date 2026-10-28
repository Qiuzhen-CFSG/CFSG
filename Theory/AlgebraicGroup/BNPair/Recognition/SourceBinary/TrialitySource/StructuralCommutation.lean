module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.TrialitySource.WeylPinning
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Positive triality commutation from the structural radical

Let B,C,E,F be the long simple, first conjugated short, first conjugated
long and highest long roots in two compatible source rank-one pinnings.
Suppose B,C lie in V, V' lies in F, [B,E]=F, and [B,F]=[C,E]=1.
The short Weyl element gives [E,F]=1. Hall--Witt applied to B,E,C
then gives [C,F]=1. The same two Weyl automorphisms transport these
relations to all ten commuting positive pairs. Thus these ten equations
need not be separate inputs to the coefficient reconstruction.

The literal quotient application supplies V as the canonical short radical
and the four subgroup assertions from Fong--Seitz I (6E)(b), printed p.43;
compare II (9.22), printed p.217. The braid and orthogonal stabilizers
inside RankOnePair remain earlier pinning obligations. No field-size or
perfectness restriction is imposed; in particular q=2 is retained.
-/

@[expose] public noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
variable {F Y : Type*} [Field F] [CharP F 2] [Group Y] {σ : F ≃+* F}
local notation "K" => ScalarMarking.SourceFixed (σ := σ)
namespace RankOnePair
variable (p : RankOnePair σ Y)

structure PositiveCommutations : Prop where
  short0_long1 : ∀ a b, Commute (p.s 0 a) (p.l 1 b)
  short0_long2 : ∀ a b, Commute (p.s 0 a) (p.l 2 b)
  long0_short1 : ∀ a b, Commute (p.l 0 a) (p.s 1 b)
  long0_short2 : ∀ a b, Commute (p.l 0 a) (p.s 2 b)
  long0_long2 : ∀ a b, Commute (p.l 0 a) (p.l 2 b)
  short1_long1 : ∀ a b, Commute (p.s 1 a) (p.l 1 b)
  short1_long2 : ∀ a b, Commute (p.s 1 a) (p.l 2 b)
  short2_long1 : ∀ a b, Commute (p.s 2 a) (p.l 1 b)
  short2_long2 : ∀ a b, Commute (p.s 2 a) (p.l 2 b)
  long1_long2 : ∀ a b, Commute (p.l 1 a) (p.l 2 b)

private theorem commute_of_bot {A B : Subgroup Y} (h : ⁅A,B⁆ = ⊥)
    {x y : Y} (hx : x ∈ A) (hy : y ∈ B) : Commute x y :=
  (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h) hx) y hy).symm

private theorem bot_of_commute {A B : Subgroup Y}
    (h : ∀ x ∈ A, ∀ y ∈ B, Commute x y) : ⁅A,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx
  exact mem_centralizer_iff.mpr (fun y hy => (h x hx y hy).symm.eq)

/-- The radical bound and three literal 6E(b) subgroup statements force all
positive commutations, via Hall--Witt and the same source Weyl elements. -/
theorem positiveCommutations_of_radical (V : Subgroup Y)
    (hB : (p.longOrbit 0).range ≤ V) (hC : (p.shortOrbit 1).range ≤ V)
    (hV : ⁅V,V⁆ ≤ (p.longOrbit 2).range)
    (hBE : ⁅(p.longOrbit 0).range,(p.longOrbit 1).range⁆ = (p.longOrbit 2).range)
    (hBF : ⁅(p.longOrbit 0).range,(p.longOrbit 2).range⁆ = ⊥)
    (hCE : ⁅(p.shortOrbit 1).range,(p.longOrbit 1).range⁆ = ⊥) :
    p.PositiveCommutations := by
  have hA (b : K) : p.dihedral.A (p.l 2 b) = p.l 2 b := p.orthogonalLong b
  have hBfix (a : F) : p.dihedral.B (p.s 2 a) = p.s 2 a := p.orthogonalShort a
  have bf (a b : K) : Commute (p.l 0 a) (p.l 2 b) :=
    commute_of_bot hBF ⟨_,rfl⟩ ⟨_,rfl⟩
  have ce (a : F) (b : K) : Commute (p.s 1 a) (p.l 1 b) :=
    commute_of_bot hCE ⟨_,rfl⟩ ⟨_,rfl⟩
  have ef (a b : K) : Commute (p.l 1 a) (p.l 2 b) := by
    have ht := (bf a b).map p.dihedral.A.toMonoidHom
    change Commute (p.dihedral.A (p.l 0 a)) (p.dihedral.A (p.l 2 b)) at ht
    simpa only [hA, ← p.l_one, ← p.s_two] using ht
  have hEF : ⁅(p.longOrbit 1).range,(p.longOrbit 2).range⁆ = ⊥ := by
    apply bot_of_commute
    rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
    exact ef a.toAdd b.toAdd
  have hCF : ⁅(p.shortOrbit 1).range,(p.longOrbit 2).range⁆ = ⊥ := by
    have hEC : ⁅(p.longOrbit 1).range,(p.shortOrbit 1).range⁆ = ⊥ := by
      rw [commutator_comm, hCE]
    have hCBE : ⁅⁅(p.shortOrbit 1).range,(p.longOrbit 0).range⁆,
        (p.longOrbit 1).range⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (commutator_mono ((commutator_mono hC hB).trans hV) le_rfl).trans
        (by rw [commutator_comm, hEF])
    have hh := commutator_commutator_eq_bot_of_rotate
      (H₁ := (p.longOrbit 0).range) (H₂ := (p.longOrbit 1).range)
      (H₃ := (p.shortOrbit 1).range) (by rw [hEC, commutator_bot_left]) hCBE
    rw [hBE, commutator_comm] at hh
    exact hh
  have cf (a : F) (b : K) : Commute (p.s 1 a) (p.l 2 b) :=
    commute_of_bot hCF ⟨_,rfl⟩ ⟨_,rfl⟩
  have ae (a : F) (b : K) : Commute (p.s 0 a) (p.l 1 b) := by
    have ht := (cf a b).map p.dihedral.B.toMonoidHom
    change Commute (p.dihedral.B (p.s 1 a)) (p.dihedral.B (p.l 2 b)) at ht
    simpa only [p.s_one, p.l_two, p.dihedral.B_B] using ht
  have af (a : F) (b : K) : Commute (p.s 0 a) (p.l 2 b) := by
    have ht := (ce a b).map p.dihedral.B.toMonoidHom
    change Commute (p.dihedral.B (p.s 1 a)) (p.dihedral.B (p.l 1 b)) at ht
    simpa only [p.s_one, p.dihedral.B_B, ← p.l_two] using ht
  have df (a : F) (b : K) : Commute (p.s 2 a) (p.l 2 b) := by
    have ht := (cf a b).map p.dihedral.A.toMonoidHom
    change Commute (p.dihedral.A (p.s 1 a)) (p.dihedral.A (p.l 2 b)) at ht
    simpa only [hA, ← p.l_one, ← p.s_two] using ht
  have de (a : F) (b : K) : Commute (p.s 2 a) (p.l 1 b) := by
    have ht := (df a b).map p.dihedral.B.toMonoidHom
    change Commute (p.dihedral.B (p.s 2 a)) (p.dihedral.B (p.l 2 b)) at ht
    simpa only [hBfix, p.l_two, p.dihedral.B_B] using ht
  have bc (a : K) (b : F) : Commute (p.l 0 a) (p.s 1 b) := by
    have ht := (de b a).map p.dihedral.A.toMonoidHom
    change Commute (p.dihedral.A (p.s 2 b)) (p.dihedral.A (p.l 1 a)) at ht
    simpa only [p.s_two, p.l_one, p.dihedral.A_A] using ht.symm
  have bd (a : K) (b : F) : Commute (p.l 0 a) (p.s 2 b) := by
    have ht := (ce b a).map p.dihedral.A.toMonoidHom
    change Commute (p.dihedral.A (p.s 1 b)) (p.dihedral.A (p.l 1 a)) at ht
    simpa only [p.l_one, p.dihedral.A_A, ← p.s_two] using ht.symm
  exact ⟨ae, af, bc, bd, bf, ce, cf, de, df, ef⟩

/-- Faithfulness of the original long rank-one map implies injectivity on its
highest positive root; no new coefficient uniqueness assumption is needed. -/
theorem longOrbit_injective (h : Function.Injective p.longMap) (i : Fin 3) :
    Function.Injective (p.longOrbit i) := by
  have h0 : Function.Injective p.longBase := by
    intro x y he
    apply Multiplicative.toAdd.injective
    exact Theory.PSL2.SemilinearCoverage.uni_injective (h he)
  fin_cases i
  · exact h0
  · exact p.dihedral.A.injective.comp h0
  · exact p.dihedral.B.injective.comp (p.dihedral.A.injective.comp h0)
end RankOnePair
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.TrialitySource
