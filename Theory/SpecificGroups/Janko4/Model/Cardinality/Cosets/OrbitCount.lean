module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.Orbit
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite certificates for the concrete J₄ vector orbit

A finite family of distinct binary vectors certifies the orbit if it contains
the base vector, is closed under the two source matrices, and has a rooted
parent forest whose edges are source-matrix multiplications. The decreasing
rank proves that every listed vector is reachable. Closure proves that all
orbit vectors are listed: the finite matrix group is generated as a monoid by
its source generators, so inverse transitions need no separate certificate.

This module proves the certificate checker, not the existence of a certificate
with 173067389 entries. In particular, the numerical index at
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/J4G1-max1W1 is not used as a
proof of the cardinality. The concrete vector and coordinate convention are
those of `Cosets.Orbit` and `Model.Data`.
-/

@[expose] public section
namespace Janko4.Cardinality

/-- One forward step in the original binary row coordinates. -/
def cosetVectorStep (b : Bool) (v : CosetVector) : CosetVector :=
  Matrix.vecMul v (if b then matrixB else matrixA)

@[simp] theorem vectorRight_sourceGenerators
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (b : Bool) (v : CosetVector) :
    vectorRight v (sourceGenerators hA hB b) = cosetVectorStep b v := by
  cases b <;> rfl

/-- Forward closure already contains the full orbit. No inverse transitions,
group order, or stabilizer identification are needed. -/
theorem cosetOrbitMap_mem_of_closed
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (S : Set CosetVector) (hbase : cosetBaseVector ∈ S)
    (hstep : ∀ b v, v ∈ S → cosetVectorStep b v ∈ S) (g : Model) :
    cosetOrbitMap g ∈ S := by
  have hgen : Submonoid.closure (Set.range (sourceGenerators hA hB)) = ⊤ := by
    rw [← Subgroup.closure_toSubmonoid_of_finite, sourceGenerators_generate]
    rfl
  have hg : g ∈ Submonoid.closure (Set.range (sourceGenerators hA hB)) := by
    rw [hgen]
    trivial
  have hpres : ∀ v, v ∈ S → vectorRight v g ∈ S := by
    induction hg using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      intro v hv
      simpa only [vectorRight_sourceGenerators] using hstep b v hv
    | one =>
      intro v hv
      simpa only [vectorRight_one] using hv
    | mul x y _ _ hx hy =>
      intro v hv
      rw [vectorRight_mul]
      exact hy _ (hx _ hv)
  exact hpres _ hbase

/-- A finite enumeration certificate consists only of actual binary vectors,
source-matrix transitions, separation, and a rooted forest. Its cardinality
is the number of indices, with no assumed orbit-membership field. -/
structure CosetVectorOrbitCertificate (ι : Type*) where
  point : ι → CosetVector
  root : ι
  root_eq : point root = cosetBaseVector
  rank : ι → ℕ
  parent : ∀ i, i ≠ root → ∃ j b,
    rank j < rank i ∧ cosetVectorStep b (point j) = point i
  closed : ∀ i b, ∃ j, cosetVectorStep b (point i) = point j
  separate : Function.Injective point

namespace CosetVectorOrbitCertificate

/-- The decreasing parent rank certifies reachability of every listed vector. -/
theorem point_mem_orbit {ι : Type*} (C : CosetVectorOrbitCertificate ι)
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) (i : ι) :
    C.point i ∈ Set.range cosetOrbitMap := by
  have h : ∀ n i, C.rank i = n → C.point i ∈ Set.range cosetOrbitMap := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      by_cases hir : i = C.root
      · subst i
        exact ⟨1, cosetOrbitMap_one.trans C.root_eq.symm⟩
      · obtain ⟨j, b, hj, hstep⟩ := C.parent i hir
        obtain ⟨g, hg⟩ := ih (C.rank j) (hi ▸ hj) j rfl
        refine ⟨g * sourceGenerators hA hB b, ?_⟩
        change vectorRight cosetBaseVector (g * sourceGenerators hA hB b) = C.point i
        rw [vectorRight_mul, show vectorRight cosetBaseVector g = C.point j from hg,
          vectorRight_sourceGenerators, hstep]
  exact h (C.rank i) i rfl

/-- Forward closure and rooted reachability identify the family with the
actual matrix orbit. -/
theorem range_eq_orbit {ι : Type*} (C : CosetVectorOrbitCertificate ι)
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Set.range C.point = Set.range cosetOrbitMap := by
  apply Set.Subset.antisymm
  · rintro v ⟨i, rfl⟩
    exact C.point_mem_orbit hA hB i
  · rintro v ⟨g, rfl⟩
    apply cosetOrbitMap_mem_of_closed hA hB (Set.range C.point)
    · exact ⟨C.root, C.root_eq⟩
    · rintro b v ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := C.closed i b
      exact ⟨j, hj.symm⟩

/-- The checker yields the exact cardinality, once an actual certificate is
provided. This theorem does not assert that such a certificate exists. -/
theorem card_eq {ι : Type*} (C : CosetVectorOrbitCertificate ι)
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card CosetVectorOrbit = Nat.card ι := by
  let f : ι → CosetVectorOrbit := fun i => ⟨C.point i, C.point_mem_orbit hA hB i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact C.separate (congrArg Subtype.val hij)
    · rintro ⟨v, hv⟩
      have hv' : v ∈ Set.range C.point := by
        rw [C.range_eq_orbit hA hB]
        exact hv
      obtain ⟨i, hi⟩ := hv'
      exact ⟨i, Subtype.ext hi⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

/-- A certificate indexed by the desired finite ordinal would close the
numerical orbit obligation in the coset construction. -/
theorem card_eq_173067389 (C : CosetVectorOrbitCertificate (Fin 173067389))
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Nat.card CosetVectorOrbit = 173067389 := by
  simpa only [Nat.card_fin] using C.card_eq hA hB

end CosetVectorOrbitCertificate
end Janko4.Cardinality
