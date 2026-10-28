module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Geometry
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Monomial

/-!
# The block action of an imprimitive unitary subgroup

An internal direct sum of nonzero subspaces permuted by the actual SU lift
has a canonical permutation action, since its summands are distinct.
Their dimensions add to four. The sum of all summands of a fixed dimension
is invariant, so irreducibility forces equal dimensions: four lines or two
planes. Choosing nonzero vectors in the four lines gives a genuine basis.
The block permutation quotient is solvable, as a subgroup of S₄.

No orthogonality or nondegeneracy is assumed. This is the geometric part of
the imprimitive case in the proper-section obligation of Aschbacher–Smith,
Theorem 0.1.2(4), condition K, printed pp.4 and 482 of `refs/quasithin.pdf`.
The unitary conventions are those of GLS3, §2.7.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Module

/-- The data of the published imprimitivity predicate, with no condition on
restriction of the Hermitian form. -/
structure ImprimitivitySystem (U : Subgroup (Carrier 4)) (r : ℕ) where
  summand : Fin r → Submodule FiniteField.Nine (Fin 4 → FiniteField.Nine)
  one_lt : 1 < r
  nonzero : ∀ i, summand i ≠ ⊥
  independent : iSupIndep summand
  spanning : (⨆ i, summand i) = ⊤
  permuted : ∀ g : fullPreimage U, ∃ σ : Equiv.Perm (Fin r),
    ∀ i, (summand i).map (liftedRepresentation U g) = summand (σ i)

theorem IsImprimitive.exists_system {U : Subgroup (Carrier 4)} (h : IsImprimitive U) :
    ∃ r, Nonempty (ImprimitivitySystem U r) := by
  obtain ⟨r, W, hr, h0, hi, ht, hp⟩ := h
  exact ⟨r, ⟨⟨W, hr, h0, hi, ht, hp⟩⟩⟩

namespace ImprimitivitySystem
variable {U : Subgroup (Carrier 4)} {r : ℕ} (B : ImprimitivitySystem U r)

/-- Uniqueness of a target summand makes the chosen permutations multiplicative. -/
@[expose] def permutationHom : fullPreimage U →* Equiv.Perm (Fin r) where
  toFun g := (B.permuted g).choose
  map_one' := by
    apply Equiv.ext
    intro i
    apply B.independent.injective B.nonzero
    have h := ((B.permuted 1).choose_spec i).symm
    exact h.trans (by simp only [map_one]; exact Submodule.map_id _)
  map_mul' g k := by
    apply Equiv.ext
    intro i
    apply B.independent.injective B.nonzero
    change B.summand ((B.permuted (g * k)).choose i) =
      B.summand ((B.permuted g).choose ((B.permuted k).choose i))
    rw [← (B.permuted (g * k)).choose_spec i,
      ← (B.permuted g).choose_spec ((B.permuted k).choose i),
      ← (B.permuted k).choose_spec i, ← Submodule.map_comp, map_mul]
    rfl

theorem map_summand (g : fullPreimage U) (i : Fin r) :
    (B.summand i).map (liftedRepresentation U g) =
      B.summand (B.permutationHom g i) := (B.permuted g).choose_spec i

theorem finrank_permutation (g : fullPreimage U) (i : Fin r) :
    finrank FiniteField.Nine (B.summand (B.permutationHom g i)) =
      finrank FiniteField.Nine (B.summand i) := by
  rw [← B.map_summand]
  exact (LinearEquiv.ofBijective (liftedRepresentation U g)
    ((liftedRepresentation U).apply_bijective g)).finrank_map_eq _

theorem sum_finrank : (∑ i, finrank FiniteField.Nine (B.summand i)) = 4 := by
  have h := (B.independent.linearEquiv B.spanning).finrank_eq
  change finrank FiniteField.Nine (DirectSum (Fin r) (fun i => B.summand i)) = _ at h
  rw [Module.finrank_directSum] at h
  simpa using h

theorem finrank_pos (i : Fin r) : 0 < finrank FiniteField.Nine (B.summand i) := by
  exact Module.finrank_pos_iff.mpr ((B.summand i).nontrivial_iff_ne_bot.mpr (B.nonzero i))

/-- Summands of any one dimension span an invariant subspace. Irreducibility
therefore forces every summand to have that same dimension. -/
theorem finrank_eq (hred : ¬ IsReducible U) (i j : Fin r) :
    finrank FiniteField.Nine (B.summand i) =
      finrank FiniteField.Nine (B.summand j) := by
  by_contra hne
  let I := {k : Fin r // finrank FiniteField.Nine (B.summand k) =
    finrank FiniteField.Nine (B.summand i)}
  let V : Submodule FiniteField.Nine (Fin 4 → FiniteField.Nine) :=
    ⨆ k : I, B.summand k.val
  have hi : B.summand i ≤ V := le_iSup_of_le ⟨i, rfl⟩ le_rfl
  have hj : Disjoint (B.summand j) V := by
    apply (B.independent j).mono_right
    refine iSup_le fun k => le_iSup_of_le k.val (le_iSup_of_le ?_ le_rfl)
    intro he
    exact hne (he ▸ k.property.symm)
  apply hred
  refine ⟨V, ?_, ?_, ?_⟩
  · intro hV
    exact B.nonzero i (le_bot_iff.mp (hV ▸ hi))
  · intro hV
    rw [hV, disjoint_top] at hj
    exact B.nonzero j hj
  · intro g hg v hv
    change liftedRepresentation U ⟨g, hg⟩ v ∈ V
    have hm : V.map (liftedRepresentation U ⟨g, hg⟩) ≤ V := by
      rw [Submodule.map_iSup]
      refine iSup_le fun k => ?_
      rw [B.map_summand]
      exact le_iSup_of_le ⟨B.permutationHom ⟨g, hg⟩ k.val,
        (B.finrank_permutation ⟨g, hg⟩ k.val).trans k.property⟩ le_rfl
    exact hm (Submodule.mem_map_of_mem hv)

/-- A decomposition of a four-space into nonzero summands has at most four blocks. -/
theorem card_le_four (B : ImprimitivitySystem U r) : r ≤ 4 := by
  calc
    r = ∑ _i : Fin r, 1 := by simp
    _ ≤ ∑ i : Fin r, finrank FiniteField.Nine (B.summand i) :=
      Finset.sum_le_sum fun i _ => B.finrank_pos i
    _ = 4 := B.sum_finrank

/-- The only irreducible imprimitivity systems in dimension four consist of
four lines or two planes. -/
theorem dimension_cases (hred : ¬ IsReducible U) :
    (r = 4 ∧ ∀ i, finrank FiniteField.Nine (B.summand i) = 1) ∨
      (r = 2 ∧ ∀ i, finrank FiniteField.Nine (B.summand i) = 2) := by
  have hr := B.one_lt
  have hb := B.card_le_four
  have he (i : Fin r) : r * finrank FiniteField.Nine (B.summand i) = 4 := by
    have hs := B.sum_finrank
    have hc : (fun k => finrank FiniteField.Nine (B.summand k)) =
        (fun _ : Fin r => finrank FiniteField.Nine (B.summand i)) :=
      funext fun k => B.finrank_eq hred k i
    rw [hc] at hs
    simpa using hs
  have hr' : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr' with h2 | h3 | h4
  · exact Or.inr ⟨h2, fun i => by have h := he i; simp only [h2] at h; omega⟩
  · have h := he ⟨0, by omega⟩
    simp only [h3] at h
    omega
  · exact Or.inl ⟨h4, fun i => by have h := he i; simp only [h4] at h; omega⟩


/-- The outer quotient is a subgroup of a solvable permutation group on at most
four letters; normality here is relative to the full SU preimage. -/
theorem permutationQuotient_isSolvable :
    Group.IsSolvable (fullPreimage U ⧸ B.permutationHom.ker) := by
  let e := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb B.card_le_four)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin r)) :=
    Group.isSolvable_of_isSolvable_injective (f := e)
      (Equiv.Perm.viaEmbeddingHom_injective _)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (QuotientGroup.quotientKerEquivRange B.permutationHom).toMonoidHom)
    (QuotientGroup.quotientKerEquivRange B.permutationHom).injective

/-- Four independent lines give an actual basis, irrespective of their
Hermitian pairings. -/
theorem isMonomial_of_lines (B : ImprimitivitySystem U 4)
    (hd : ∀ i, finrank FiniteField.Nine (B.summand i) = 1) : IsMonomial U := by
  classical
  have hn (i : Fin 4) := (B.summand i).ne_bot_iff.mp (B.nonzero i)
  choose v hv hv0 using hn
  have hspan (i : Fin 4) : B.summand i = Submodule.span FiniteField.Nine {v i} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (hd i) (hv i) (hv0 i)
  have hli : LinearIndependent FiniteField.Nine v :=
    B.independent.linearIndependent B.summand hv hv0
  have hs : ⊤ ≤ Submodule.span FiniteField.Nine (Set.range v) := by
    rw [← B.spanning]
    refine iSup_le fun i => ?_
    rw [hspan i]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self i))
  let b := Module.Basis.mk hli hs
  refine ⟨b, fun g => ⟨B.permutationHom g, fun i => ?_⟩⟩
  have hm : liftedRepresentation U g (v i) ∈ B.summand (B.permutationHom g i) := by
    rw [← B.map_summand]
    exact Submodule.mem_map_of_mem (hv i)
  rw [hspan, Submodule.mem_span_singleton] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, ?_, ?_⟩
  · intro ha0
    have hz : liftedRepresentation U g (v i) = 0 := by simpa [ha0] using ha.symm
    exact hv0 i (((liftedRepresentation U).apply_bijective g).injective
      (hz.trans (map_zero _).symm))
  · simpa only [b, Module.Basis.mk_apply] using ha.symm

end ImprimitivitySystem

/-- The line case is already a monomial representation; only the two-plane
system remains for the stabilizer calculation. -/
theorem IsImprimitive.monomial_or_two_planes {U : Subgroup (Carrier 4)}
    (h : IsImprimitive U) (hred : ¬ IsReducible U) :
    IsMonomial U ∨ ∃ B : ImprimitivitySystem U 2,
      ∀ i, finrank FiniteField.Nine (B.summand i) = 2 := by
  obtain ⟨r, ⟨B⟩⟩ := h.exists_system
  rcases B.dimension_cases hred with ⟨rfl, hd⟩ | ⟨rfl, hd⟩
  · exact Or.inl (B.isMonomial_of_lines hd)
  · exact Or.inr ⟨B, hd⟩

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
