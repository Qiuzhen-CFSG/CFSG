module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Ambient

/-!
# Wedge annihilators and determinantal flag conditions

For an arbitrary projective exterior vector, its annihilator is the kernel of
left exterior multiplication by vectors of the original space. The codomain
is the actual next exterior power. Intersections of two annihilators are
kernels of stacked maps, so their dimension bounds are ordinary matrix rank
bounds, independent of representatives.

For genuine Plücker lines these subspaces recover the original subspaces;
the mixed dimension bound is therefore exactly inclusion. This supplies the
incidence comparison for Borel, *Linear Algebraic Groups*, §11.1. The separate
assertions that the self-rank condition forces decomposability and that the
rank bounds define closed scheme loci are not assumed or asserted here.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

/-- Multiplication on the left by a vector, valued in the correct exterior grade. -/
def wedgeVectorMap {d : ℕ} (a : ⋀[k]^d V) : V →ₗ[k] ⋀[k]^(d+1) V :=
  ((LinearMap.mulRight k (a : ExteriorAlgebra k V)).comp (ExteriorAlgebra.ι k)).codRestrict _
    (fun v => by
      change ExteriorAlgebra.ι k v * (a : ExteriorAlgebra k V) ∈
        LinearMap.range (ExteriorAlgebra.ι k) ^ (d+1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ v) a.property)

@[simp] theorem wedgeVectorMap_coe {d : ℕ} (a : ⋀[k]^d V) (v : V) :
    (wedgeVectorMap a v : ExteriorAlgebra k V) =
      ExteriorAlgebra.ι k v * (a : ExteriorAlgebra k V) := rfl

@[simp] theorem mem_ker_wedgeVectorMap {d : ℕ} (a : ⋀[k]^d V) (v : V) :
    v ∈ LinearMap.ker (wedgeVectorMap a) ↔
      ExteriorAlgebra.ι k v * (a : ExteriorAlgebra k V) = 0 := by
  rw [LinearMap.mem_ker, ← Subtype.coe_inj]
  rfl

/-- The subspace annihilating an exterior line. No decomposability is assumed. -/
def pluckerAnnihilator {d : ℕ} (p : ℙ k (⋀[k]^d V)) : Submodule k V where
  carrier := {v | ∀ a ∈ p.submodule,
    ExteriorAlgebra.ι k v * (a : ExteriorAlgebra k V) = 0}
  zero_mem' := by simp
  add_mem' hx hy := by
    intro a ha
    rw [map_add, add_mul, hx a ha, hy a ha, add_zero]
  smul_mem' c v hv := by
    intro a ha
    rw [map_smul, Algebra.smul_mul_assoc, hv a ha, smul_zero]

@[simp] theorem mem_pluckerAnnihilator {d : ℕ} (p : ℙ k (⋀[k]^d V)) (v : V) :
    v ∈ pluckerAnnihilator p ↔ ∀ a ∈ p.submodule,
      ExteriorAlgebra.ι k v * (a : ExteriorAlgebra k V) = 0 := Iff.rfl

/-- Any generator of the line gives the same wedge kernel. -/
theorem pluckerAnnihilator_eq_ker_of_span {d : ℕ} (p : ℙ k (⋀[k]^d V))
    (a : ⋀[k]^d V) (ha : p.submodule = k ∙ a) :
    pluckerAnnihilator p = LinearMap.ker (wedgeVectorMap a) := by
  ext v
  rw [mem_pluckerAnnihilator, mem_ker_wedgeVectorMap, ha]
  constructor
  · intro h
    exact h a (Submodule.mem_span_singleton_self _)
  · intro h z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [Submodule.coe_smul, Algebra.mul_smul_comm, h, smul_zero]

theorem pluckerAnnihilator_eq_ker {d : ℕ} (p : ℙ k (⋀[k]^d V)) :
    pluckerAnnihilator p = LinearMap.ker (wedgeVectorMap p.rep) :=
  pluckerAnnihilator_eq_ker_of_span p p.rep p.submodule_eq

@[simp] theorem pluckerAnnihilator_mk {d : ℕ} (a : ⋀[k]^d V) (ha : a ≠ 0) :
    pluckerAnnihilator (Projectivization.mk k a ha) =
      LinearMap.ker (wedgeVectorMap a) :=
  pluckerAnnihilator_eq_ker_of_span _ a (Projectivization.submodule_mk a ha)

/-- Simultaneous annihilation is the kernel of the stacked wedge maps. -/
theorem pluckerAnnihilator_inf_eq_ker {d e : ℕ}
    (p : ℙ k (⋀[k]^d V)) (q : ℙ k (⋀[k]^e V)) :
    pluckerAnnihilator p ⊓ pluckerAnnihilator q =
      LinearMap.ker ((wedgeVectorMap p.rep).prod (wedgeVectorMap q.rep)) := by
  rw [LinearMap.ker_prod, pluckerAnnihilator_eq_ker, pluckerAnnihilator_eq_ker]

variable [FiniteDimensional k V]

@[simp] theorem pluckerAnnihilator_subspacePlucker (d : ℕ) (W : Submodule k V)
    (hW : Module.finrank k W = d) :
    pluckerAnnihilator (subspacePlucker d W hW) = W := by
  ext v
  rw [mem_pluckerAnnihilator, subspacePlucker_submodule,
    ← mem_iff_wedge_pluckerLine d W hW]

/-- The mixed rank condition is actual subspace inclusion on decomposable lines. -/
theorem pluckerAnnihilator_incidence_iff (d e : ℕ) (W U : Submodule k V)
    (hW : Module.finrank k W = d) (hU : Module.finrank k U = e) :
    d ≤ Module.finrank k ↥(pluckerAnnihilator (subspacePlucker d W hW) ⊓
      pluckerAnnihilator (subspacePlucker e U hU)) ↔ W ≤ U := by
  rw [pluckerAnnihilator_subspacePlucker, pluckerAnnihilator_subspacePlucker]
  constructor
  · intro h
    have hinf : W ⊓ U = W := Submodule.eq_of_le_of_finrank_le inf_le_left (by simpa only [hW] using h)
    exact hinf.symm.le.trans inf_le_right
  · intro h
    rw [inf_eq_left.mpr h, hW]

/-- Rank-nullity makes the simultaneous annihilator condition determinantal. -/
theorem pluckerAnnihilator_inf_finrank_iff {d e : ℕ}
    (p : ℙ k (⋀[k]^d V)) (q : ℙ k (⋀[k]^e V)) (r : ℕ)
    (hr : r ≤ Module.finrank k V) :
    r ≤ Module.finrank k ↥(pluckerAnnihilator p ⊓ pluckerAnnihilator q) ↔
      Module.finrank k (LinearMap.range
        ((wedgeVectorMap p.rep).prod (wedgeVectorMap q.rep))) ≤
          Module.finrank k V - r := by
  rw [pluckerAnnihilator_inf_eq_ker]
  have h := LinearMap.finrank_range_add_finrank_ker
    ((wedgeVectorMap p.rep).prod (wedgeVectorMap q.rep))
  omega

/-- The minors used for the flag locus test every pair of ordered degrees,
including each degree paired with itself. -/
def FlagRankConditions
    (p : (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)) : Prop :=
  ∀ i j : Fin (Module.finrank k V), i ≤ j → (i : ℕ) ≤
    Module.finrank k ↥(pluckerAnnihilator (p i) ⊓ pluckerAnnihilator (p j))

omit [FiniteDimensional k V] in
/-- The diagonal pair gives the required lower bound on each annihilator. -/
theorem FlagRankConditions.le_finrank_annihilator
    {p : (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)}
    (h : FlagRankConditions p) (i : Fin (Module.finrank k V)) :
    (i : ℕ) ≤ Module.finrank k (pluckerAnnihilator (p i)) := by
  calc
    (i : ℕ) ≤ Module.finrank k ↥(pluckerAnnihilator (p i) ⊓
        pluckerAnnihilator (p i)) := h i i le_rfl
    _ = Module.finrank k (pluckerAnnihilator (p i)) :=
      congrArg (fun S : Submodule k V => Module.finrank k S) (inf_idem _)

/-- The finite list of flag conditions is a list of rank bounds on stacked
linear maps, with the original ambient dimension as the number of columns. -/
theorem flagRankConditions_iff_stacked_rank
    (p : (i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)) :
    FlagRankConditions p ↔ ∀ i j : Fin (Module.finrank k V), i ≤ j →
      Module.finrank k (LinearMap.range
        ((wedgeVectorMap (p i).rep).prod (wedgeVectorMap (p j).rep))) ≤
          Module.finrank k V - (i : ℕ) := by
  constructor
  · intro h i j hij
    exact (pluckerAnnihilator_inf_finrank_iff (p i) (p j) i
      (Nat.le_of_lt i.isLt)).mp (h i j hij)
  · intro h i j hij
    exact (pluckerAnnihilator_inf_finrank_iff (p i) (p j) i
      (Nat.le_of_lt i.isLt)).mpr (h i j hij)

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
