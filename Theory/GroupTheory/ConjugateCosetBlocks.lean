module
public import Theory.GroupTheory.ConjugateCosetOrbit
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugate cosets as blocks

Let `M` be a finite subgroup and let the centralizer of `j` normalize `M`
and intersect it trivially. Then the left coset `jM` is a block under
conjugation: any two of its conjugates are equal or disjoint. This supplies
Brauer, *On finite Desarguesian planes I*, (2B), article page 119, for the
point and line sets in his incidence geometry.

Conjugation by `j` is fixed-point-free on `M`. The surjectivity of its
commutator map identifies `jM` with the conjugation orbit of `j` under `M`,
as supplied by `orbit_conjugate_eq_coset`.
Adjoining the centralizer does not change that orbit, because the centralizer
normalizes `M`, and the resulting subgroup contains the stabilizer of `j`.
Mathlib's subgroup-orbit block theorem now gives the conclusion.

Brauer assumes `j` is an involution. The reduction here does not need that
additional hypothesis: the fixed-point-free commutator-map argument applies
to any `j`. The left-coset action is ordinary multiplication; the block action
uses `ConjAct G` explicitly so these two actions are kept distinct.
-/

open scoped Pointwise

namespace Theory.GroupTheory

private theorem isBlock_orbit_of_stabilizer_normalizes
    {G X : Type*} [Group G] [MulAction G X] (M : Subgroup G) (a : X)
    (hn : MulAction.stabilizer G a ≤ Subgroup.normalizer (M : Set G)) :
    MulAction.IsBlock G (MulAction.orbit M a) := by
  have heq : MulAction.orbit ↥(M ⊔ MulAction.stabilizer G a) a =
      MulAction.orbit M a := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      have hh := h.property
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hh
      obtain ⟨m, hm, c, hc, hmc⟩ := hh
      refine ⟨⟨m, hm⟩, ?_⟩
      change m • a = (h : G) • a
      rw [← hmc, mul_smul, MulAction.mem_stabilizer_iff.mp hc]
    · rintro ⟨m, rfl⟩
      exact ⟨⟨m, (show M ≤ M ⊔ MulAction.stabilizer G a from le_sup_left) m.property⟩, rfl⟩
  rw [← heq]
  exact MulAction.IsBlock.of_orbit le_sup_right

/-- A centralizer-normalized subgroup disjoint from the centralizer gives a
conjugation block by taking the corresponding left coset. -/
public theorem isBlock_conjugate_coset_of_centralizer_normalizes
    {G : Type*} [Group G] (M : Subgroup G) [Finite M] (j : G)
    (hn : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hd : Disjoint M (Subgroup.centralizer ({j} : Set G))) :
    MulAction.IsBlock (ConjAct G) (j • (M : Set G)) := by
  let N : Subgroup (ConjAct G) := M.map ConjAct.toConjAct.toMonoidHom
  have hn' : MulAction.stabilizer (ConjAct G) j ≤
      Subgroup.normalizer (N : Set (ConjAct G)) := by
    intro c hc
    have hfix : ConjAct.ofConjAct c * j * (ConjAct.ofConjAct c)⁻¹ = j := hc
    have hcen : ConjAct.ofConjAct c ∈ Subgroup.centralizer ({j} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)
    apply M.le_normalizer_map ConjAct.toConjAct.toMonoidHom
    exact ⟨ConjAct.ofConjAct c, hn hcen, rfl⟩
  rw [← orbit_conjugate_eq_coset M j hn hd]
  exact isBlock_orbit_of_stabilizer_normalizes N j hn'

end Theory.GroupTheory
