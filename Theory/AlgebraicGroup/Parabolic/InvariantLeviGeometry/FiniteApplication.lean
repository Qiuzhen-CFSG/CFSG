module

public import Theory.AlgebraicGroup.Parabolic.InvariantLeviGeometry.RootTransport
public import Theory.SpecificGroups.LieType.InvariantParabolicLevi

/-!
# The constructed standard factors in finite Levi descent

This applies the closed root-generated parabolic construction to the literal
finite projection of `InvariantParabolicLevi`. Root collection supplies
containment, relative normality, unipotence and pointwise `U L` multiplication;
the induced root-ray action supplies invariance. Only geometric disjointness
and, for the p-core conclusion, the finite Levi p-core remain explicit.

Source: GLS3, Theorems 1.13.3(a,b) and 2.6.5(e,g).
-/

namespace Theory.AlgebraicGroup.InvariantLeviGeometry

open FiniteParabolicRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
  {K : Variety k} [AlgebraicGroup K]
  (S : StandardParabolicRelativeRootSetup K)
  (σ : AlgebraicEndomorphism K) (p : ℕ) [Fact p.Prime] [CharP k p]

local notation "hD" => S.standardParabolic.left.right.left
local notation "hT" => S.standardParabolic.left.left.left
local notation "P" => parabolic S.D hD hT S.positiveRoots S.sigmaJ
local notation "U" => unipotent S.D hD S.positiveRoots S.sigmaJ
local notation "L" => levi S.D hD hT S.sigmaJ

/-- Actual application to the finite Levi projection: the algebraic source
premises already established here are discharged for the constructed factors. -/
public theorem exists_finiteProjection
    (hpositive : S.positiveRoots = S.D.positive)
    (hdis : Disjoint (U).toSubgroup (L).toSubgroup)
    (hσU : (U).toSubgroup.map σ.onPoints = (U).toSubgroup)
    (hσL : (L).toSubgroup.map σ.onPoints = (L).toSubgroup) :
    ∃ f : restrict σ p (P).toSubgroup →* restrict σ p (L).toSubgroup,
      Function.Surjective f ∧
      f.ker = (restrict σ p (U).toSubgroup).subgroupOf (restrict σ p (P).toSubgroup) ∧
      ∀ l : restrict σ p (L).toSubgroup,
        f ⟨l, restrict_mono σ p (factors_le S.D hD hT S.positiveRoots S.sigmaJ).2
          l.property⟩ = l := by
  apply InvariantParabolicLevi.exists_finiteLeviProjection σ p P U L
    (factors_le S.D hD hT S.positiveRoots S.sigmaJ).2 (unipotent_normal S)
    (unipotent_isUnipotent S hpositive) hdis
  · intro u hu
    change σ.onPoints u ∈ (U).toSubgroup
    rw [← hσU]
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · intro l hl
    change σ.onPoints l ∈ (L).toSubgroup
    rw [← hσL]
    exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
  · intro x hx
    exact (mem_parabolic_iff S x).mp hx

/-- Application to the literal relative p-core convention of the parent.
Disjointness and the finite reductive p-core theorem are still independent
source obligations, rather than fields assumed in the constructed factors. -/
public theorem restricted_unipotent_eq_pCore
    [Fact (IsAlgebraicSteinbergEndomorphism σ)]
    (hpositive : S.positiveRoots = S.D.positive)
    (hdis : Disjoint (U).toSubgroup (L).toSubgroup)
    (hσU : (U).toSubgroup.map σ.onPoints = (U).toSubgroup)
    (hσL : (L).toSubgroup.map σ.onPoints = (L).toSubgroup)
    (hLcore : pCore p (restrict σ p (L).toSubgroup) = ⊥) :
    restrict σ p (U).toSubgroup =
      (pCore p (restrict σ p (P).toSubgroup)).map (restrict σ p (P).toSubgroup).subtype := by
  obtain ⟨f, hf, hker, -⟩ := exists_finiteProjection S σ p hpositive hdis hσU hσL
  exact restrict_eq_embedded_pCore_of_leviProjection σ p P U
    (factors_le S.D hD hT S.positiveRoots S.sigmaJ).1
    (unipotent_isUnipotent S hpositive) f hf hker hLcore

/-- The induced root-ray permutation preserving `J` discharges both invariance
premises of the finite projection for the actual constructed standard factors. -/
public theorem exists_finiteProjection_of_rootRays
    (hpositive : S.positiveRoots = S.D.positive)
    (hdis : Disjoint (U).toSubgroup (L).toSubgroup)
    (e : S.D.Root ≃ S.D.Root) (A : S.XQ ≃ₗ[ℚ] S.XQ)
    (c : S.D.Root → ℚ) (hc : ∀ a, c a ≠ 0)
    (hray : ∀ a, A (S.rationalPairing.root (S.rootEquiv a)) =
      c a • S.rationalPairing.root (S.rootEquiv (e a)))
    (hroot : ∀ a, (S.D.rootSubgroup a).toSubgroup.map σ.onPoints =
      (S.D.rootSubgroup (e a)).toSubgroup)
    (htorus : S.T.toSubgroup.map σ.onPoints = S.T.toSubgroup)
    (hpos : e '' S.positiveRoots = S.positiveRoots)
    (hJ : e '' S.J = S.J) (hneg : ∀ a, e (S.D.neg a) = S.D.neg (e a)) :
    ∃ f : restrict σ p (P).toSubgroup →* restrict σ p (L).toSubgroup,
      Function.Surjective f ∧
      f.ker = (restrict σ p (U).toSubgroup).subgroupOf (restrict σ p (P).toSubgroup) ∧
      ∀ l : restrict σ p (L).toSubgroup,
        f ⟨l, restrict_mono σ p (factors_le S.D hD hT S.positiveRoots S.sigmaJ).2
          l.property⟩ = l := by
  have hσ := standard_candidates_map_eq S σ.onPoints e A c hc hray hroot
    htorus hpos hJ hneg
  exact exists_finiteProjection S σ p hpositive hdis hσ.2.1 hσ.2.2

end Theory.AlgebraicGroup.InvariantLeviGeometry
