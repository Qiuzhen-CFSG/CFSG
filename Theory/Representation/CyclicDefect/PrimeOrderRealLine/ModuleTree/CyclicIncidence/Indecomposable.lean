module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Indecomposable.Contracts
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Indecomposable.CornerPartition
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Combinatorics

/-!
# From actual block corners to connected decomposition incidence

Every ordinary row is nonzero, as follows by evaluating its restriction at
the identity. A separating partition of rows therefore induces a nonempty
proper partition of columns. All mixed entries of `DᵀD` vanish. If corner
dimensions are the degree-weighted entries of this Gram matrix, both corner
directions across the induced partition vanish, contrary to primitivity.

This is the final algebraic and combinatorial assembly in Feit I.17.9 and
VII.6.4. The theorems below are conditional on a block idempotent frame and
its corner-rank comparison. Constructing the frame and proving that comparison
are separate obligations; these theorems do not assert their existence.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m}

/-- A genuine ordinary decomposition row cannot be zero: its value at the
identity is the positive dimension of an irreducible ordinary module. -/
theorem multiplicity_row_nonzero (a : Decomposition d residue L n)
    (v : {i // i ∈ d.block}) : ∃ e, a.multiplicity v e ≠ 0 := by
  have hχ := d.complete.1 v.val
  obtain ⟨k, ρ, hρ⟩ := hχ.1
  let : Representation.IsIrreducible ρ :=
    (irreducible_iff_character_norm_one ρ).mpr (by simpa [hρ] using hχ.2)
  let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  let : Nontrivial (Fin k → ℂ) := Function.Injective.nontrivial ρ.asModuleEquiv.injective
  have hdegree : d.chi v.val (ConjClasses.mk 1) ≠ 0 := by
    rw [hρ]
    change ρ.character 1 ≠ 0
    rw [Representation.char_one]
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Fin k → ℂ)).ne'
  by_contra h
  push Not at h
  have hrestriction := a.restriction 1
    (by simpa using (Fact.out : p.Prime).ne_one) v
  simp only [h, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at hrestriction
  exact hdegree hrestriction

/-- The literal Cartan corner-rank identity rules out separating row sets.
No endpoint, cyclic-defect, or graph hypothesis is used in this implication. -/
theorem crossing_of_corner_ranks (a : Decomposition d residue L n)
    (hprincipal : ModularBlock.IsCentrallyPrimitive (reducedPrincipal d residue))
    (q : BlockIdempotentFrame a)
    (hrank : ∀ e f, Module.finrank K (q.corner e f) =
      a.degree e * a.degree f *
        ∑ v : {i // i ∈ d.block}, a.multiplicity v e * a.multiplicity v f)
    (S : Finset {i // i ∈ d.block}) (hS : S.Nonempty) (hproper : S ≠ Finset.univ) :
    ∃ e v w, v ∈ S ∧ w ∉ S ∧
      a.multiplicity v e ≠ 0 ∧ a.multiplicity w e ≠ 0 := by
  by_contra hcross
  let T : Finset (Fin n) := Finset.univ.filter fun e =>
    ∃ v ∈ S, a.multiplicity v e ≠ 0
  have hTmem (e : Fin n) : e ∈ T ↔ ∃ v ∈ S, a.multiplicity v e ≠ 0 := by
    simp [T]
  have houtside (e : Fin n) (he : e ∈ T)
      (w : {i // i ∈ d.block}) (hw : w ∉ S) : a.multiplicity w e = 0 := by
    obtain ⟨v, hv, hve⟩ := (hTmem e).mp he
    by_contra hwe
    exact hcross ⟨e, v, w, hv, hw, hve, hwe⟩
  have hinside (f : Fin n) (hf : f ∉ T)
      (v : {i // i ∈ d.block}) (hv : v ∈ S) : a.multiplicity v f = 0 := by
    by_contra hvf
    exact hf ((hTmem f).mpr ⟨v, hv, hvf⟩)
  have hT : T.Nonempty := by
    obtain ⟨v, hv⟩ := hS
    obtain ⟨e, he⟩ := multiplicity_row_nonzero a v
    exact ⟨e, (hTmem e).mpr ⟨v, hv, he⟩⟩
  have hTproper : T ≠ Finset.univ := by
    intro hTuniv
    have hall : S = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro w
      by_contra hw
      obtain ⟨e, he⟩ := multiplicity_row_nonzero a w
      exact he (houtside e (hTuniv ▸ Finset.mem_univ e) w hw)
    exact hproper hall
  have hgram (e f : Fin n) (he : e ∈ T) (hf : f ∉ T) :
      ∑ v : {i // i ∈ d.block}, a.multiplicity v e * a.multiplicity v f = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : v ∈ S
    · rw [hinside f hf v hv, mul_zero]
    · rw [houtside e he v hv, zero_mul]
  obtain ⟨e, f, x, he, hf, hcorner⟩ :=
    ModularBlock.exists_cross_corner_of_isCentrallyPrimitive _ hprincipal
      q.element q.idempotent q.nonzero q.orthogonal q.sum_eq T hT hTproper
  have hef : Module.finrank K (q.corner e f) = 0 := by
    rw [hrank e f, hgram e f he hf, mul_zero]
  have hfe : Module.finrank K (q.corner f e) = 0 := by
    rw [hrank f e]
    simp_rw [Nat.mul_comm (a.multiplicity _ f) (a.multiplicity _ e)]
    rw [hgram e f he hf, mul_zero]
  exact hcorner.elim
    (fun h => h (q.mul_eq_zero_of_corner_finrank_zero e f hef x))
    (fun h => h (q.mul_eq_zero_of_corner_finrank_zero f e hfe x))

/-- Actual application to arbitrary endpoints of this same decomposition.
Only this graph consumer assumes the zero-one endpoint formula. -/
theorem endpointGraph_connected_of_corner_ranks (a : Decomposition d residue L n)
    (hprincipal : ModularBlock.IsCentrallyPrimitive (reducedPrincipal d residue))
    (q : BlockIdempotentFrame a)
    (hrank : ∀ e f, Module.finrank K (q.corner e f) =
      a.degree e * a.degree f *
        ∑ v : {i // i ∈ d.block}, a.multiplicity v e * a.multiplicity v f)
    (left right : Fin n → {i // i ∈ d.block})
    (hne : ∀ e, left e ≠ right e)
    (hmult : ∀ v e, a.multiplicity v e =
      if v = left e ∨ v = right e then 1 else 0) :
    (endpointGraph left right).Connected := by
  let : Nonempty {i // i ∈ d.block} := ⟨⟨d.principal, d.principal_mem⟩⟩
  apply endpointGraph_connected_of_crossing a.multiplicity left right hne
    (hcross := crossing_of_corner_ranks a hprincipal q hrank)
  intro v e
  by_cases hv : v = left e ∨ v = right e
  · simpa only [if_pos hv] using hmult v e
  · simpa only [if_neg hv] using hmult v e

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
