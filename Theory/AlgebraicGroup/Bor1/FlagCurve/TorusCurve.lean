module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.ClosedCurveIso
public import Theory.AlgebraicGroup.Bor1.FlagCurve.NormalizedWeights
public import Theory.AlgebraicGroup.Bor1.FlagCurve.SourceTransport
public import Theory.AlgebraicGroup.Bor1.FlagCurve.BasisChangeIso

/-!
# Identifying the original normal torus curve

A moving one-dimensional torus supplies two occupied weights in the actual
rational representation. Dividing their differences by the occupied gcd
preserves the unit orbit over the algebraically closed field, including in
positive characteristic. The original curve keeps its carrier; an invertible
basis change exposes the coprime monomial charts. The normal-curve theorem
then gives its scheme isomorphism with the projective line over the field.

Source: Borel, Linear Algebraic Groups, §13.13(3–4).
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open scoped LinearAlgebra.Projectivization
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
open SeparatingBorel.ProjectiveLimit
universe u
variable {k E : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup E] [Module k E] [FiniteDimensional k E]
variable {G : Variety k} [AlgebraicGroup G]

set_option backward.isDefEq.respectTransparency false

theorem exists_projectiveLine_iso_of_torus_curve
    {Y : Variety.Geometric k} (hY : IsIrreducible Y) (hN : IsNormal Y)
    (hdim : dimension Y = 1)
    (i : Variety.Geometric.Morphism Y (projectiveSpace k E)) [IsClosedImmersion i.hom]
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsSubtorus T)
    (c : ClosedSubgroupTorusCocharacter T) (hc : Function.Surjective c.onPoints)
    (A : MorphicAction G (projectiveSpace k E))
    (b₀ : Module.Basis (Fin (Module.finrank k E)) k E)
    (he : ∀ g p, projectiveSpacePointEquivOf b₀ (A.toMulAction.smul g p) =
      Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b₀ p))
    (v : E) (hv : v ≠ 0)
    (horbit : ∀ t : Variety.Point T.carrierVariety,
      A.toMulAction.smul (T.includePoint t)
        (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) ∈ Set.range i)
    (t : Variety.Point T.carrierVariety)
    (hmove : A.toMulAction.smul (T.includePoint t)
      (projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) ≠
      projectivePointOfVector (b₀.equivFun v) (b₀.equivFun.map_ne_zero_iff.mpr hv)) :
    ∃ e : Y.toScheme ≅ (projectiveLine k).toScheme,
      e.hom ≫ (projectiveLine k).structureMap = Y.structureMap := by
  classical
  obtain ⟨b, χ, hweight⟩ := exists_finite_torus_weight_basis ρ hρ T hT
  let m := fun l => characterCocharacterPairing T c (Additive.ofMul (χ l))
  obtain ⟨M, h, hM⟩ := exists_largest_occupied_weight b m v hv
  obtain ⟨a, ha, hca⟩ := h
  let n := fun l => (M - m l).toNat
  have hna : n a = 0 := by simp [n, ha]
  obtain ⟨d, hnd, hcd⟩ := exists_occupied_positive_exponent ρ T c hc A b₀ b χ he hweight
    M v hv ⟨a, ha, hca⟩ hM t hmove
  obtain ⟨n', N, d', s, hNpos, hna', hnd', hcd', has, hcs, hgcd, hbound, hrange⟩ :=
    exists_normalized_monomial_weights (b.equivFun v) n a d hna hca hnd hcd
  let j := i.comp (projectiveBasisChange b b₀)
  have : IsIso (projectiveBasisChange b b₀).hom := projectiveBasisChange_isIso b b₀
  have : IsClosedImmersion j.hom := by
    change IsClosedImmersion (i.hom ≫ (projectiveBasisChange b b₀).hom)
    infer_instance
  have hraw (u : kˣ) : monomialCurve (b.equivFun v) n ⟨a, hna, hca⟩
      (affinePoint (u : k)) ∈ Set.range j := by
    obtain ⟨y, hy⟩ := horbit (c.onPoints (cocharacterParameter (Units.mk0 (u : k) u.ne_zero)⁻¹))
    refine ⟨y, ?_⟩
    have heq := topCurve_basisChange_nonzero ρ T c A b₀ b χ he hweight M v hv
      ⟨a, ha, hca⟩ hM (u : k) u.ne_zero
    exact (Variety.Geometric.Morphism.comp_apply_point i (projectiveBasisChange b b₀) y).trans
      ((congrArg (fun q => projectiveBasisChange b b₀ q) hy).trans heq.symm)
  apply exists_projectiveLine_iso_of_monomial_units hY hN hdim j
    (b.equivFun v) n' N hNpos a d' hna' hnd' hca hcd' hbound s has hcs hgcd
  intro z hz
  have hzrange : (fun l => b.equivFun v l * z ^ n' l) ∈
      Set.range (fun u : kˣ => fun l => b.equivFun v l * (u : k) ^ n l) := by
    rw [hrange]
    exact ⟨Units.mk0 z hz, rfl⟩
  obtain ⟨u, hu⟩ := hzrange
  have heq : monomialCurve (b.equivFun v) n' ⟨a, hna', hca⟩ (affinePoint z) =
      monomialCurve (b.equivFun v) n ⟨a, hna, hca⟩ (affinePoint (u : k)) := by
    obtain ⟨hv', he'⟩ := monomialCurve_point (b.equivFun v) n' ⟨a, hna', hca⟩ z
    obtain ⟨hv₀, he₀⟩ := monomialCurve_point (b.equivFun v) n ⟨a, hna, hca⟩ (u : k)
    rw [he', he₀]
    apply (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mpr
    apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
    exact ⟨1, by simpa only [one_smul] using hu⟩
  have hmem := (j.point_mem_range_iff_closedPoint_mem_range _).mp (hraw u)
  exact Eq.mp (congrArg (fun p : Point (projectiveSpace k E) =>
    p.1 (IsLocalRing.closedPoint k) ∈ Set.range j.hom) heq.symm) hmem

end Theory.AlgebraicGroup.Bor1.FlagCurve
