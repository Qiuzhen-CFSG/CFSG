module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Indecomposable.Contracts
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.Indecomposable.Frames.Radical
public import Theory.Representation.FiniteSimpleDensity

/-!
# Orthogonal idempotents for the supplied block simples

Every supplied complete, pairwise inequivalent family of simple modules
has a block idempotent frame in the literal group algebra. The theorem
works over any algebraically closed field and with any residue map and
root lift occurring in `Decomposition`.

Simultaneous density first realizes the identity on one simple and zero
on all others. Multiplication by the central block projector puts these
selectors in the block ideal. Completeness shows that their idempotency
and orthogonality errors belong to the Jacobson radical, so their images
in the semisimple quotient are orthogonal idempotents. The nilpotent-radical
lifting theorem lifts the whole family simultaneously. Multiplying the
lifts by the block projector preserves orthogonality and their simple
actions. Their sum equals the block projector because these are commuting
idempotents with nilpotent difference.

Thus each element includes every primitive copy with the specified simple
head; neither centrality nor primitivity of the frame elements is asserted.
This is the frame used by the I.13.11 block-linkage argument, not that
linkage theorem itself. Source: Feit, *The Representation Theory of Finite
Groups*, I.12.1--4 and I.13.5--7, 11.
-/

public section
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
open ModularBlock.PrimeBlockConstruction Representation.BlockFrames
variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m n : ℕ}
    {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m}

/-- Completeness detects radical elements in the literal block ideal. -/
theorem block_mem_jacobson_of_simple_actions_zero
    (a : Decomposition d residue L n) {x : K[G]}
    (hx : reducedPrincipal d residue * x = x)
    (hz : ∀ i, (a.rep i).asAlgebraHom x = 0) : x ∈ Ring.jacobson K[G] := by
  apply mem_jacobson_of_simple_actions_zero
  intro k ρ hρ
  let : IsIrreducible ρ := hρ
  rcases central_idempotent_action ρ (reducedPrincipal_mem_center d residue)
    (reducedPrincipal_isIdempotent d residue) with hzero | hone
  · rw [← hx, map_mul, hzero, zero_mul]
  · obtain ⟨i, ⟨e⟩⟩ := a.complete k ρ hρ hone
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (ρ.asAlgebraHom x v) = e (0 : _)
    have h : e (ρ.asAlgebraHom x v) = (a.rep i).asAlgebraHom x (e v) :=
      (IntertwiningMap.equivLinearMapAsModule ρ (a.rep i) e.toIntertwiningMap).map_smul x v
    simpa only [hz, LinearMap.zero_apply, map_zero] using h

private theorem exists_simultaneous_actions [IsAlgClosed K]
    (a : Decomposition d residue L n)
    (f : ∀ i, Module.End K (Fin (a.degree i) → K)) :
    ∃ x : K[G], ∀ i, (a.rep i).asAlgebraHom x = f i := by
  let : ∀ i, IsIrreducible (a.rep i) := a.irreducible
  have hne : Pairwise fun i j => IsEmpty ((a.rep i).asModule ≃ₗ[K[G]] (a.rep j).asModule) := by
    intro i j hij
    refine ⟨fun e => ?_⟩
    let e' := (IntertwiningMap.equivLinearMapAsModule (a.rep i) (a.rep j)).symm e.toLinearMap
    have he' : Function.Bijective e' := e.bijective
    exact (a.inequivalent hij).false (e'.ofBijective he')
  obtain ⟨x, hx⟩ := Module.exists_simultaneous_smul_eq (F := K)
    (fun i => (a.rep i).asModule) hne
    (fun i => (a.rep i).asModuleEquiv.symm.conj (f i))
  refine ⟨x, fun i => ?_⟩
  apply LinearMap.ext
  intro v
  have h := congrArg (a.rep i).asModuleEquiv
    (hx i ((a.rep i).asModuleEquiv.symm v))
  simpa [asModuleEquiv_map_smul, LinearEquiv.conj_apply] using h

/-- Orthogonal block idempotents selecting exactly the supplied complete simple family. -/
theorem nonempty_blockIdempotentFrame [IsAlgClosed K]
    (a : Decomposition d residue L n) : Nonempty (BlockIdempotentFrame a) := by
  classical
  let b := reducedPrincipal d residue
  have hb : IsIdempotentElem b := reducedPrincipal_isIdempotent d residue
  have hc : ∀ x : K[G], Commute x b :=
    Semigroup.mem_center_iff.mp (reducedPrincipal_mem_center d residue)
  choose t ht using fun i : Fin n =>
    exists_simultaneous_actions a (fun j => if i = j then 1 else 0)
  let s : Fin n → K[G] := fun i => b * t i
  have hbs (i) : b * s i = s i := by
    dsimp [s]
    rw [← mul_assoc, hb.eq]
  have hs (i j) : (a.rep j).asAlgebraHom (s i) = if i = j then 1 else 0 := by
    dsimp [s, b]
    rw [map_mul, a.inBlock, one_mul, ht]
  let π := Ideal.Quotient.mk (Ring.jacobson K[G])
  have hπzero (x : K[G]) : π x = 0 ↔ x ∈ Ring.jacobson K[G] :=
    Ideal.Quotient.eq_zero_iff_mem
  have hπnil : ∀ x ∈ RingHom.ker π, IsNilpotent x := by
    intro x hx
    exact nilpotent_of_mem_jacobson ((hπzero x).mp hx)
  have horth : OrthogonalIdempotents (fun i => π (s i)) := by
    constructor
    · intro i
      change π (s i) * π (s i) = π (s i)
      rw [← map_mul, ← sub_eq_zero, ← map_sub, hπzero]
      apply block_mem_jacobson_of_simple_actions_zero a
      · change b * (s i * s i - s i) = _
        rw [mul_sub, ← mul_assoc, hbs]
      · intro j
        simp only [map_sub, map_mul, hs]
        split <;> simp
    · intro i j hij
      rw [← map_mul, hπzero]
      apply block_mem_jacobson_of_simple_actions_zero a
      · change b * (s i * s j) = _
        rw [← mul_assoc, hbs]
      · intro k
        simp only [map_mul, hs]
        by_cases hi : i = k
        · subst k
          simp [Ne.symm hij]
        · simp [hi]
  obtain ⟨q, hq, hqπ⟩ := horth.lift_of_isNilpotent_ker π hπnil
    (fun i => ⟨s i, rfl⟩)
  have hqaction (i j) : (a.rep j).asAlgebraHom (q i) = if i = j then 1 else 0 := by
    have hdiff : q i - s i ∈ Ring.jacobson K[G] := by
      apply (hπzero _).mp
      rw [map_sub, show π (q i) = π (s i) from congrFun hqπ i, sub_self]
    let : IsIrreducible (a.rep j) := a.irreducible j
    have h := simple_action_zero_of_mem_jacobson (a.rep j) hdiff
    rwa [map_sub, sub_eq_zero, hs] at h
  let e : Fin n → K[G] := fun i => b * q i
  have he : OrthogonalIdempotents e := by
    constructor
    · intro i
      exact IsIdempotentElem.mul_of_commute (hc (q i)).symm hb (hq.idem i)
    · intro i j hij
      change (b * q i) * (b * q j) = 0
      calc
        _ = (b * b) * (q i * q j) := (hc (q i)).mul_mul_mul_comm b (q j)
        _ = 0 := by rw [hq.ortho hij, mul_zero]
  have heaction (i j) : (a.rep j).asAlgebraHom (e i) = if i = j then 1 else 0 := by
    dsimp [e, b]
    rw [map_mul, a.inBlock, one_mul, hqaction]
  have heblock (i) : b * e i = e i := by
    dsimp [e]
    rw [← mul_assoc, hb.eq]
  have hsum : ∑ i, e i = b := by
    have hdiff : b - ∑ i, e i ∈ Ring.jacobson K[G] := by
      apply block_mem_jacobson_of_simple_actions_zero a
      · change b * (b - ∑ i, e i) = _
        rw [mul_sub, hb.eq, Finset.mul_sum]
        simp_rw [heblock]
      · intro j
        rw [map_sub, map_sum, a.inBlock]
        simp [heaction]
    exact (eq_of_isNilpotent_sub_of_isIdempotentElem_of_commute
      hb he.isIdempotentElem_sum (nilpotent_of_mem_jacobson hdiff)
      (hc (∑ i, e i)).symm).symm
  refine ⟨⟨e, he.idem, ?_, he.ortho, hsum, heaction⟩⟩
  intro i hi
  let : IsIrreducible (a.rep i) := a.irreducible i
  let : Nontrivial (a.rep i).asModule := IsSimpleModule.nontrivial K[G] (a.rep i).asModule
  let : Nontrivial (Fin (a.degree i) → K) :=
    (a.rep i).asModuleEquiv.injective.nontrivial
  have h := heaction i i
  rw [hi, map_zero, if_pos rfl] at h
  exact zero_ne_one h

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence
