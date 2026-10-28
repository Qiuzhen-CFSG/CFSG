module
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup

/-!
# Integral adjoint restriction to a based root subsystem

A saturated embedding of root systems, together with a marked inclusion of bases,
preserves root strings and their integral Geck coefficients. Extending the basis
inclusion by zero gives an injective map of lattices. Both signed simple operators
intertwine this map: their entries agree on the block, and saturation rules out
entries leaving the block.

These geometric hypotheses are instantiated for the literal E6 roots in E7 and E8
in `Coordinates`. No representation-comparison hypothesis is part of the data.
Source: GLS3 §2.6.2, the common-lattice subsystem construction
(`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section
noncomputable section
set_option linter.unusedSectionVars false
namespace TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
open Matrix RootPairing.IntegralGeckConstruction
attribute [local instance] Classical.decEq

section Matrices
variable {m n : Type*} [Fintype m] [Fintype n] (e : m ↪ n)

/-- The integral inclusion of a subset of a basis. -/
def inclusion : Matrix n m ℤ := fun i j => if i = e j then 1 else 0

def inclusionOver (S : Type*) [CommRing S] : Matrix n m S :=
  (inclusion e).map (Int.castRingHom S)

@[simp] theorem inclusionOver_apply (S : Type*) [CommRing S] (i : n) (j : m) :
    inclusionOver e S i j = if i = e j then 1 else 0 := by
  simp [inclusionOver, inclusion]

theorem inclusion_mulVec (S : Type*) [CommRing S] (x : m → S) (i : m) :
    (inclusionOver e S *ᵥ x) (e i) = x i := by
  simp [Matrix.mulVec, dotProduct, e.injective.eq_iff]

theorem inclusion_mulVec_injective (S : Type*) [CommRing S] :
    Function.Injective (Matrix.mulVec (inclusionOver e S)) := by
  intro x y h
  funext i
  simpa only [inclusion_mulVec] using congrFun h (e i)

private theorem mul_inclusion (B : Matrix n n ℤ) (i : n) (j : m) :
    (B * inclusion e) i j = B i (e j) := by
  simp [Matrix.mul_apply, inclusion]

private theorem inclusion_mul (A : Matrix m m ℤ) (i j : m) :
    (inclusion e * A) (e i) j = A i j := by
  simp [Matrix.mul_apply, inclusion, e.injective.eq_iff]

private theorem inclusion_mul_of_notMem (A : Matrix m m ℤ) (i : n)
    (hi : i ∉ Set.range e) (j : m) : (inclusion e * A) i j = 0 := by
  have hn (k : m) : i ≠ e k := fun h => hi ⟨k, h.symm⟩
  simp [Matrix.mul_apply, inclusion, hn]

theorem intertwines_of_entries (A : Matrix m m ℤ) (B : Matrix n n ℤ)
    (hblock : ∀ i j, B (e i) (e j) = A i j)
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, B i (e j) = 0) :
    B * inclusion e = inclusion e * A := by
  ext i j
  rw [mul_inclusion]
  by_cases hi : i ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hi
    rw [inclusion_mul, hblock]
  · rw [inclusion_mul_of_notMem e A i hi, hzero i hi]
end Matrices

section RootSystems
variable {ι κ R M N M' N' : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  {P : RootPairing ι R M N} {Q : RootPairing κ R M' N'}
  [P.IsCrystallographic] [P.IsReduced] [Q.IsCrystallographic] [Q.IsReduced]
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {b : P.Base} {c : Q.Base}

/-- A based root subsystem whose ambient roots in its linear span are exactly its roots.
The weight map and the index maps concern root geometry, not group representations. -/
structure BasedEmbedding (b : P.Base) (c : Q.Base) where
  index : ι ↪ κ
  weight : M →ₗ[R] M'
  injective : Function.Injective weight
  root : ∀ i, weight (P.root i) = Q.root (index i)
  saturated : ∀ x, weight x ∈ Set.range Q.root → x ∈ Set.range P.root
  base : b.support ↪ c.support
  base_root : ∀ i : b.support, index i = (base i : κ)
  cartan : ∀ i j, c.cartanMatrix (base i) (base j) = b.cartanMatrix i j

namespace BasedEmbedding
variable (d : BasedEmbedding b c)

def indexMap : b.support ⊕ ι ↪ c.support ⊕ κ := d.base.sumMap d.index

private theorem mem_range (x : M) :
    d.weight x ∈ Set.range Q.root ↔ x ∈ Set.range P.root := by
  refine ⟨d.saturated x, ?_⟩
  rintro ⟨r, rfl⟩
  exact ⟨d.index r, (d.root r).symm⟩

private theorem linearIndependent (i j : ι) :
    LinearIndependent R ![Q.root (d.index i), Q.root (d.index j)] ↔
      LinearIndependent R ![P.root i, P.root j] := by
  have h := d.weight.linearIndependent_iff (LinearMap.ker_eq_bot.mpr d.injective)
    (v := ![P.root i, P.root j])
  have he : d.weight ∘ ![P.root i, P.root j] =
      ![Q.root (d.index i), Q.root (d.index j)] := by
    funext k
    fin_cases k <;> exact d.root _
  rwa [he] at h

@[simp] theorem chainBotCoeff (i j : ι) :
    Q.chainBotCoeff (d.index i) (d.index j) = P.chainBotCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · rw [P.chainBotCoeff_eq_sSup h,
      Q.chainBotCoeff_eq_sSup ((d.linearIndependent i j).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_sub, map_nsmul, d.root] using
      d.mem_range (P.root j - n • P.root i)
  · rw [P.chainBotCoeff_of_not_linearIndependent h,
      Q.chainBotCoeff_of_not_linearIndependent
        (fun h' => h ((d.linearIndependent i j).mp h'))]

@[simp] theorem chainTopCoeff (i j : ι) :
    Q.chainTopCoeff (d.index i) (d.index j) = P.chainTopCoeff i j := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · rw [P.chainTopCoeff_eq_sSup h,
      Q.chainTopCoeff_eq_sSup ((d.linearIndependent i j).mpr h)]
    congr 1
    ext n
    simpa only [Set.mem_ofPred_eq, map_add, map_nsmul, d.root] using
      d.mem_range (P.root j + n • P.root i)
  · rw [P.chainTopCoeff_of_not_linearIndependent h,
      Q.chainTopCoeff_of_not_linearIndependent
        (fun h' => h ((d.linearIndependent i j).mp h'))]

theorem neg_index (i : ι) :
    d.index (P.reflectionPerm i i) = Q.reflectionPerm (d.index i) (d.index i) := by
  apply Q.root.injective
  rw [← d.root, P.root_reflectionPerm, P.reflection_apply_self, map_neg,
    d.root, Q.root_reflectionPerm, Q.reflection_apply_self]

private theorem root_add_iff (i j k : ι) :
    Q.root (d.index k) = Q.root (d.index i) + Q.root (d.index j) ↔
      P.root k = P.root i + P.root j := by
  rw [← d.root, ← d.root, ← d.root, ← map_add]
  exact d.injective.eq_iff

private theorem root_sub_iff (i j k : ι) :
    Q.root (d.index k) = Q.root (d.index j) - Q.root (d.index i) ↔
      P.root k = P.root j - P.root i := by
  rw [← d.root, ← d.root, ← d.root, ← map_sub]
  exact d.injective.eq_iff

private theorem mem_index_of_root_eq (r : κ) (x : M) (h : Q.root r = d.weight x) :
    r ∈ Set.range d.index := by
  obtain ⟨s, hs⟩ := d.saturated x ⟨r, h⟩
  refine ⟨s, Q.root.injective ?_⟩
  rw [← d.root, hs, h]

private theorem notMem_base {r : c.support} (h : Sum.inl r ∉ Set.range d.indexMap) :
    ∀ i, r ≠ d.base i := by
  intro i hi
  exact h ⟨Sum.inl i, congrArg Sum.inl hi.symm⟩

private theorem notMem_index {r : κ} (h : Sum.inr r ∉ Set.range d.indexMap) :
    r ∉ Set.range d.index := by
  rintro ⟨i, rfl⟩
  exact h ⟨Sum.inr i, rfl⟩

/-- The positive integral Geck operator preserves this actual based subsystem. -/
theorem eMatrix_intertwines (i : b.support) :
    eMatrix (d.base i) * inclusion d.indexMap = inclusion d.indexMap * eMatrix i := by
  apply intertwines_of_entries
  · rintro (j | j) (k | k)
    · simp [eMatrix, indexMap]
    · simp [eMatrix, indexMap, ← d.base_root, ← d.neg_index, d.index.injective.eq_iff,
        d.base.injective.eq_iff]
    · simp [eMatrix, indexMap, ← d.base_root, d.index.injective.eq_iff, d.cartan]
    · simp [eMatrix, indexMap, ← d.base_root, d.root_add_iff]
  · rintro (j | j) hj (k | k)
    · simp [eMatrix, indexMap]
    · simp [eMatrix, indexMap, d.notMem_base hj i]
    · have hji : j ≠ d.index i := fun h => d.notMem_index hj ⟨i, h.symm⟩
      simp [eMatrix, indexMap, ← d.base_root, hji]
    · have hji : Q.root j ≠ Q.root (d.base i) + Q.root (d.index k) := by
        intro h
        apply d.notMem_index hj
        apply d.mem_index_of_root_eq j (P.root i + P.root k)
        simpa only [map_add, d.root, d.base_root] using h
      simp [eMatrix, indexMap, hji]

/-- The negative operator uses the literal negative-root Geck convention. -/
theorem fMatrix_intertwines (i : b.support) :
    fMatrix (d.base i) * inclusion d.indexMap = inclusion d.indexMap * fMatrix i := by
  apply intertwines_of_entries
  · rintro (j | j) (k | k)
    · simp [fMatrix, indexMap]
    · simp [fMatrix, indexMap, ← d.base_root, d.index.injective.eq_iff,
        d.base.injective.eq_iff]
    · simp [fMatrix, indexMap, ← d.base_root, ← d.neg_index,
        d.index.injective.eq_iff, d.cartan]
    · simp [fMatrix, indexMap, ← d.base_root, d.root_sub_iff]
  · rintro (j | j) hj (k | k)
    · simp [fMatrix, indexMap]
    · simp [fMatrix, indexMap, d.notMem_base hj i]
    · have hji : j ≠ d.index (P.reflectionPerm i i) :=
        fun h => d.notMem_index hj ⟨_, h.symm⟩
      simp [fMatrix, indexMap, ← d.base_root, ← d.neg_index, hji]
    · have hji : Q.root j ≠ Q.root (d.index k) - Q.root (d.base i) := by
        intro h
        apply d.notMem_index hj
        apply d.mem_index_of_root_eq j (P.root k - P.root i)
        simpa only [map_sub, d.root, d.base_root] using h
      simp [fMatrix, indexMap, hji]

end BasedEmbedding
end RootSystems
end TwistedE6.FoldedSubsystem.HigherRealizations.AdjointBlocks
