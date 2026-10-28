module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.Words
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.SplitTorus

/-!
# Recovering the literal F4 coroot parameters over a subfield

The actual product of the four coroot words is the diagonal torus matrix
with inverse parameters. The checked inverse Cartan equations therefore
recover each direct coroot parameter as a monomial in four presented matrix
entries. In particular, rational coordinates recover units over the same
subfield, with no root extraction or finite-field cardinality argument.

This is the torus part of Steinberg's Theorem 7 (Lemma 35 and its use on
pp. 64–65 of `refs/KGroup/GLS3/Chapter2St1.tex`). It does not claim Bruhat
coverage or recover either unipotent factor of a general carrier point.
-/

public noncomputable section

open scoped BigOperators
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters

universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Actual matrix identification, including the inverse-parameter convention. -/
theorem corootProduct_ambient (t : Fin 4 → Fˣ) :
    (F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints (corootProduct t) =
      F4Chevalley.matrixToAmbient (F4Chevalley.torusElement t⁻¹) := by
  classical
  rw [corootProduct, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, algebraicCorootElement_ambient, F4Chevalley.matrixH_simple]
  let p (i : Fin 4) := integralChevalleySimpleCorootParameter
    (typeF4RootPairing_baseEquiv i) (t i)⁻¹
  have hp : (List.ofFn p).prod = F4Chevalley.torusParameter t⁻¹ := by
    rw [List.prod_ofFn]
    funext q
    simp only [Finset.prod_apply, p, integralChevalleySimpleCorootParameter]
    have he (i : Fin 4) : q = typeF4RootPairing_baseEquiv i ↔
        i = typeF4RootPairing_baseEquiv.symm q := by
      exact (eq_comm.trans typeF4RootPairing_baseEquiv.eq_symm_apply.symm)
    simp only [he, Finset.prod_ite_eq', Finset.mem_univ, if_true,
      F4Chevalley.torusParameter, Pi.inv_apply]
  change (List.ofFn fun i =>
    (F4Chevalley.matrixToAmbient.comp F4Chevalley.torusMatrixHom) (p i)).prod =
      (F4Chevalley.matrixToAmbient.comp F4Chevalley.torusMatrixHom)
        (F4Chevalley.torusParameter t⁻¹)
  rw [← hp, map_list_prod, List.map_ofFn]
  rfl

/-- The root-diagonal entries are actual presented coordinates of the carrier. -/
theorem corootProduct_diagonal (t : Fin 4 → Fˣ) (b : F4Chevalley.BasisIndex) :
    (corootProduct t).val (Sum.inl
      (F4Chevalley.carrierIndexEquiv (k := F) b,
       F4Chevalley.carrierIndexEquiv (k := F) b)) =
      (F4Chevalley.basisTorusUnit t⁻¹ b : F) := by
  have h := congrArg (fun x : Variety.Point (F4Chevalley.Ambient F) =>
    x.val (Sum.inl (F4Chevalley.carrierIndexEquiv (k := F) b,
      F4Chevalley.carrierIndexEquiv (k := F) b))) (corootProduct_ambient t)
  change ((F4Chevalley.ambientClosedCarrier (k := F)).pointEquiv
    (corootProduct t)).val.val _ = _ at h
  rw [ClosedSubgroup.pointEquiv_val] at h
  change (corootProduct t).val _ =
    (generalLinearRepresentationPoint F4Chevalley.carrierBasis
      (Matrix.GeneralLinearGroup.toLin (F4Chevalley.torusElement t⁻¹))).val _ at h
  rw [generalLinearRepresentationPoint_matrix] at h
  simpa [F4Chevalley.carrierBasis, carrierBasis, Module.Basis.reindex_apply,
    F4Chevalley.torusElement, integralChevalleyTorusElement,
    F4Chevalley.basisTorusUnit] using h

/-- Exact parameter-recovery equation on the literal coroot word. -/
theorem corootProduct_recover (t : Fin 4 → Fˣ) (i : Fin 4) :
    (t i : F) = ∏ j : Fin 4,
      (corootProduct t).val (Sum.inl
        (F4Chevalley.carrierIndexEquiv (k := F) (Sum.inr (typeF4SimpleRootIndex j)),
         F4Chevalley.carrierIndexEquiv (k := F) (Sum.inr (typeF4SimpleRootIndex j)))) ^
          F4Chevalley.torusRecoveryExponent i j := by
  simp only [corootProduct_diagonal]
  simpa only [Pi.inv_apply, inv_inv, Units.coe_prod, Units.val_pow_eq_pow_val] using
    congrArg Units.val (F4Chevalley.basisTorusUnit_inv_recover t⁻¹ i)

theorem corootProduct_injective : Function.Injective (corootProduct (F := F)) := by
  intro t u h
  funext i
  apply Units.ext
  rw [corootProduct_recover t i, corootProduct_recover u i, h]

omit [IsAlgClosed F] in
/-- A unit whose value lies in a field image has an actual unit preimage. -/
theorem unit_mem_range_of_value {K : Type v} [Field K] (f : K →+* F)
    (t : Fˣ) (ht : (t : F) ∈ f.range) :
    t ∈ Set.range (Units.map f.toMonoidHom) := by
  obtain ⟨a, ha⟩ := ht
  have ha0 : a ≠ 0 := by
    intro hz
    exact t.ne_zero (by rw [← ha, hz, map_zero])
  exact ⟨Units.mk0 a ha0, Units.ext ha⟩

/-- Rational matrix entries recover all four actual coroot units. -/
theorem corootParameters_mem_range {K : Type v} [Field K] (f : K →+* F)
    (t : Fin 4 → Fˣ)
    (ht : ∀ c, (corootProduct t).val c ∈ f.range) (i : Fin 4) :
    t i ∈ Set.range (Units.map f.toMonoidHom) := by
  apply unit_mem_range_of_value f
  rw [corootProduct_recover]
  exact f.range.prod_mem fun j _ => f.range.pow_mem (ht _) _

/-- Every point of the literal split torus is a product of the four direct
coroot words; the statement uses no abstract root-system model. -/
theorem exists_corootProduct_of_mem_splitTorus
    {x : Variety.Point (F4Chevalley.Carrier (k := F))}
    (hx : x ∈ F4Chevalley.splitTorus (k := F)) :
    ∃ t : Fin 4 → Fˣ, corootProduct t = x := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨(dPointEquiv 4 z)⁻¹, ?_⟩
  apply (F4Chevalley.ambientClosedCarrier (k := F)).inclusion_injective
  rw [corootProduct_ambient, inv_inv, F4Chevalley.splitTorusMorphism_inclusion_apply,
    F4Chevalley.torusAmbientMorphism_apply]
  rfl

/-- Constructive rational torus parameters, ready for finite word transport. -/
theorem exists_rational_corootProduct {K : Type v} [Field K] (f : K →+* F)
    {x : Variety.Point (F4Chevalley.Carrier (k := F))}
    (hx : x ∈ F4Chevalley.splitTorus (k := F)) (hrat : ∀ c, x.val c ∈ f.range) :
    ∃ t : Fin 4 → Kˣ, corootProduct (fun i => Units.map f.toMonoidHom (t i)) = x := by
  obtain ⟨u, rfl⟩ := exists_corootProduct_of_mem_splitTorus hx
  choose t ht using corootParameters_mem_range f u hrat
  exact ⟨t, congrArg corootProduct (funext ht)⟩

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters
