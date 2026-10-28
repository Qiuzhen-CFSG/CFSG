module

public import Theory.AlgebraicGroup.Automorphisms.Steinberg
public import Theory.AlgebraicGroup.Parabolic.Defs
public import Theory.AlgebraicGroup.RootData.StandardParabolicGenerated
public import Theory.AlgebraicGroup.Unipotent.DefiningCharacteristic
public import Theory.GroupTheory.FiniteParabolicTransfer

/-!
# Finite-point constructions for Lie-type parabolics

The finite group in a GLS sigma-setup is `O^{p'}(K^sigma)`, not in general
the full fixed-point group. We use the actual prime-to-p residual and its
inclusion into the algebraic point group. Closed unipotent subgroups restrict
to p-subgroups; their fixed points already lie in this residual, so no
unipotent elements are lost. A Levi projection onto a p-reduced group then
identifies the restricted radical with the embedded p-core.

The root-generated parabolic candidate includes the torus. Without it, the
empty-index candidate would only be the positive unipotent subgroup, rather
than the Borel. Parabolicity of these candidates, the finite positive Sylow
theorem, existence of the Levi projections and the invariant-parabolic
correspondence remain separate geometric inputs. This file does not certify
them, nor define a Lie-type family by those conclusions.

Source: GLS3, 2.2.1, 2.3.4, 2.6.4--2.6.8; Aschbacher--Smith I.2.5,
printed p.414. The prime-to-p residual is not the derived subgroup; the
exceptional small derived groups require separate comparison theorems.
-/

@[expose] public section

namespace Theory.AlgebraicGroup.FiniteParabolicRealization

variable {k : Type*} [Field k] {K : Variety k} [AlgebraicGroup K]

/-- The full fixed-point subgroup; this need not be the group of a sigma-setup. -/
abbrev fixedPoints (σ : AlgebraicEndomorphism K) : Subgroup (Variety.Point K) :=
  σ.onPoints.eqLocus (MonoidHom.id _)

instance finite_fixedPoints (σ : AlgebraicEndomorphism K)
    [hσ : Fact (IsAlgebraicSteinbergEndomorphism σ)] : Finite (fixedPoints σ) :=
  hσ.out.2

/-- The group occurring in the source sigma-setup, once the algebraic group
is semisimple and sigma is Steinberg. No structural conclusions are fields. -/
abbrev definingGroup (σ : AlgebraicEndomorphism K) (p : ℕ) :=
  Subgroup.primeToResidual p (fixedPoints σ)

def pointEmbedding (σ : AlgebraicEndomorphism K) (p : ℕ) :
    definingGroup σ p →* Variety.Point K :=
  (fixedPoints σ).subtype.comp (definingGroup σ p).subtype

theorem pointEmbedding_injective (σ : AlgebraicEndomorphism K) (p : ℕ) :
    Function.Injective (pointEmbedding σ p) :=
  Subtype.coe_injective.comp Subtype.coe_injective

/-- Intersection of an algebraic point subgroup with the source finite group. -/
def restrict (σ : AlgebraicEndomorphism K) (p : ℕ)
    (H : Subgroup (Variety.Point K)) : Subgroup (definingGroup σ p) :=
  H.comap (pointEmbedding σ p)

theorem restrict_mono (σ : AlgebraicEndomorphism K) (p : ℕ)
    {H L : Subgroup (Variety.Point K)} (h : H ≤ L) :
    restrict σ p H ≤ restrict σ p L := Subgroup.comap_mono h

/-- Relative normality survives intersection with the finite group. -/
theorem restrict_normal (σ : AlgebraicEndomorphism K) (p : ℕ)
    (P U : Subgroup (Variety.Point K)) (hN : (U.subgroupOf P).Normal) :
    ((restrict σ p U).subgroupOf (restrict σ p P)).Normal := by
  let f : restrict σ p P →* P :=
    { toFun := fun x => ⟨pointEmbedding σ p x, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact hN.comap f

/-- The source definition relative to the specified finite Borel. Applications
must supply the actual invariant algebraic Borel and its finite realization. -/
def IsFiniteParabolic (σ : AlgebraicEndomorphism K) (p : ℕ)
    (B : ClosedSubgroup K) (P : Subgroup (definingGroup σ p)) : Prop :=
  ∃ g : definingGroup σ p,
    (restrict σ p B.toSubgroup).map (MulAut.conj g).toMonoidHom ≤ P

/-- The algebraic side of GLS3 2.6.8, using exact sigma-invariance.
The equivalence with `IsFiniteParabolic` is not built into either definition. -/
def IsInvariantParabolicRestriction (σ : AlgebraicEndomorphism K) (p : ℕ)
    (P : Subgroup (definingGroup σ p)) : Prop :=
  ∃ Q : ClosedSubgroup K, IsParabolicSubgroup Q ∧
    Q.toSubgroup.map σ.onPoints = Q.toSubgroup ∧ restrict σ p Q.toSubgroup = P

theorem IsFiniteParabolic.contains_sylow
    (σ : AlgebraicEndomorphism K) (p : ℕ)
    [Fact (IsAlgebraicSteinbergEndomorphism σ)] [Fact p.Prime]
    {B : ClosedSubgroup K} {P : Subgroup (definingGroup σ p)}
    (hP : IsFiniteParabolic σ p B P)
    (S : Sylow p (definingGroup σ p))
    (hS : (S : Subgroup _) ≤ restrict σ p B.toSubgroup) :
    ∃ R : Sylow p (definingGroup σ p), (R : Subgroup _) ≤ P := by
  obtain ⟨g, hg⟩ := hP
  exact Subgroup.contains_sylow_of_conjugate_le S hS g hg

/-- Torus plus the standard root factors. Actual parabolicity still requires
the based root datum and the source standard-position hypotheses. -/
noncomputable def rootParabolicCandidate
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (positiveRoots sigmaJ : Set D.Root) : Subgroup (Variety.Point K) :=
  T.toSubgroup ⊔ standardParabolicRootFactor D positiveRoots sigmaJ

theorem torus_le_rootParabolicCandidate
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (positiveRoots sigmaJ : Set D.Root) :
    T.toSubgroup ≤ rootParabolicCandidate D positiveRoots sigmaJ := le_sup_left

theorem positive_le_rootParabolicCandidate
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (positiveRoots sigmaJ : Set D.Root) :
    RootSubgroupGenerated D positiveRoots ≤
      rootParabolicCandidate D positiveRoots sigmaJ := by
  apply le_trans (RootSubgroupGenerated_mono D ?_) le_sup_right
  intro α hα
  exact Or.inl (Or.inl hα)

theorem radical_le_rootParabolicCandidate
    {T : ClosedSubgroup K} (D : RootGroupData K T)
    (positiveRoots sigmaJ : Set D.Root) :
    standardUnipotentRootFactor D positiveRoots sigmaJ ≤
      rootParabolicCandidate D positiveRoots sigmaJ :=
  (standardUnipotentRootFactor_le_standardParabolicRootFactor D
    positiveRoots sigmaJ).trans le_sup_right

@[simp] theorem rootParabolicCandidate_empty
    {T : ClosedSubgroup K} (D : RootGroupData K T) (positiveRoots : Set D.Root) :
    rootParabolicCandidate D positiveRoots ∅ =
      T.toSubgroup ⊔ RootSubgroupGenerated D positiveRoots := by
  simp [rootParabolicCandidate, standardParabolicRootFactor]

section Unipotent

variable [IsAlgClosed k] (σ : AlgebraicEndomorphism K) (p : ℕ)
  [Fact p.Prime] [CharP k p]

/-- Restriction of an actual algebraic unipotent subgroup is a p-subgroup. -/
theorem restrict_isPGroup (U : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    IsPGroup p (restrict σ p U.toSubgroup) :=
  (U.isPGroup_of_unipotent hU p).comap_of_injective
    (pointEmbedding σ p) (pointEmbedding_injective σ p)

/-- The restricted unipotent radical lies in the finite parabolic p-core
before a Levi decomposition or p-reducedness theorem is available. -/
theorem restrict_le_embedded_pCore (P U : ClosedSubgroup K)
    (hUP : U.toSubgroup ≤ P.toSubgroup)
    (hN : (U.toSubgroup.subgroupOf P.toSubgroup).Normal)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    restrict σ p U.toSubgroup ≤
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype := by
  have hle : (restrict σ p U.toSubgroup).subgroupOf (restrict σ p P.toSubgroup) ≤
      pCore p (restrict σ p P.toSubgroup) :=
    le_sSup ⟨restrict_normal σ p _ _ hN, (restrict_isPGroup σ p U hU).comap_subtype⟩
  have hm := Subgroup.map_mono (f := (restrict σ p P.toSubgroup).subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le (restrict_mono σ p hUP)] at hm

/-- All fixed unipotent elements belong to the prime-to-p residual. -/
theorem fixed_unipotent_le_definingGroup (U : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    U.toSubgroup.comap (fixedPoints σ).subtype ≤ definingGroup σ p :=
  Subgroup.le_primeToResidual_of_isPGroup
    ((U.isPGroup_of_unipotent hU p).comap_of_injective
      (fixedPoints σ).subtype Subtype.coe_injective)

/-- The source group and the full fixed-point group have identical
intersections with every closed unipotent subgroup. -/
theorem map_restrict_unipotent (U : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety) :
    (restrict σ p U.toSubgroup).map (definingGroup σ p).subtype =
      U.toSubgroup.comap (fixedPoints σ).subtype :=
  Subgroup.map_subgroupOf_eq_of_le (fixed_unipotent_le_definingGroup σ p U hU)

/-- A nonidentity fixed root element witnesses nontriviality after restriction.
Existence of that element for every proper parabolic is a separate root theorem. -/
theorem restrict_ne_bot_of_fixed_unipotent (U : ClosedSubgroup K)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (x : Variety.Point K) (hx : x ∈ U.toSubgroup)
    (hfix : σ.onPoints x = x) (hne : x ≠ 1) :
    restrict σ p U.toSubgroup ≠ ⊥ := by
  let y : definingGroup σ p :=
    ⟨⟨x, hfix⟩, fixed_unipotent_le_definingGroup σ p U hU hx⟩
  intro hbot
  have hy : y ∈ restrict σ p U.toSubgroup := hx
  rw [hbot] at hy
  exact hne (congrArg (pointEmbedding σ p) (show y = 1 from hy))

/-- A geometric Levi projection with p-reduced finite target identifies the
restricted unipotent subgroup with the embedded p-core of the finite parabolic. -/
theorem restrict_eq_embedded_pCore_of_leviProjection
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (P U : ClosedSubgroup K) (hUP : U.toSubgroup ≤ P.toSubgroup)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    {L : Type*} [Group L] [Finite L]
    (f : restrict σ p P.toSubgroup →* L) (hf : Function.Surjective f)
    (hker : f.ker = (restrict σ p U.toSubgroup).subgroupOf
      (restrict σ p P.toSubgroup)) (hL : pCore p L = ⊥) :
    restrict σ p U.toSubgroup =
      (pCore p (restrict σ p P.toSubgroup)).map (restrict σ p P.toSubgroup).subtype :=
  (Subgroup.embedded_pCore_eq_of_leviProjection _ _ (restrict_mono σ p hUP)
    f hf hker (restrict_isPGroup σ p U hU) hL).symm

end Unipotent

end Theory.AlgebraicGroup.FiniteParabolicRealization

end
