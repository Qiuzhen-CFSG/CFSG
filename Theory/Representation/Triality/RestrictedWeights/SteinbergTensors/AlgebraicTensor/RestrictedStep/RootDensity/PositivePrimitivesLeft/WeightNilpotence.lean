module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine

/-!
# Integral weights and joint positive-root nilpotence

The first coefficient of a pinned root action shifts a left torus weight by
that root's integral coroot coordinates. The functional
`3 μ₀ + 5 μ₁ + 3 μ₂ + 3 μ₃` agrees with root height, hence every positive
operator raises it by at least one. Independent weight spaces in a finite
representation have finite support. A word longer than the range of heights
therefore vanishes on every spanning weight space.

Negative cyclicity supplies the spanning decomposition used here. No Lie
homomorphism in characteristic zero or inference from individual nilpotence
is used. Raw characters are inverted exactly by `leftWeightEmbedding`.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §§2.8–2.9,
4.5 and 11.1, underlying GLS3 Theorem 2.8.5 and Corollary 2.8.6(a).
Adapted from the F4 `PositivePrimitives/WeightNilpotence.lean` height argument.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
@[expose] public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
namespace PositivePrimitivesLeft

/-- The actual torus weight space, indexed by left integral coordinates. -/
def integralWeightSpace (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (μ : Weight) : Submodule k V := weightSpace ρ S.torus (S.leftWeightEmbedding μ)

omit [IsAlgClosed k] in
/-- Distinct integral weights give independent subspaces. -/
theorem integralWeightSpace_iSupIndep (S : D4Geometry K) (ρ : RationalRepresentation K V) :
    iSupIndep (integralWeightSpace S ρ) :=
  (weightSpace_iSupIndep ρ S.torus).comp S.leftWeightEmbedding.injective

/-- Integral coroot coordinates of a root, with positive height for positive roots. -/
def rootWeight (S : D4Geometry K) (α : S.roots.Root) : Weight :=
  fun i => S.roots.pairing α (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))

omit [IsAlgClosed k] in
/-- The direct root character is the inverse of the raw root character. -/
theorem rootWeight_character (S : D4Geometry K) (α : S.roots.Root) :
    S.leftWeightEmbedding (rootWeight S α) = (S.roots.rootWeight α)⁻¹ := by
  obtain ⟨a, ha⟩ := S.characters.surjective (S.roots.rootWeight α)
  have hcoord : a.toAdd = rootWeight S α := by
    funext i
    rw [← S.coroot_coordinates a.toAdd i]
    change S.roots.weightPairing (S.characters a) _ = _
    rw [ha]
    exact S.realized.weightPairing_rootWeight α _
  rw [S.leftWeightEmbedding_eq_inv, ← hcoord]
  exact congrArg Inv.inv ha

/-- The integral height functional for the numbered D4 Cartan matrix. -/
def weightHeight : Weight →ₗ[ℤ] ℤ where
  toFun μ := 3 * μ 0 + 5 * μ 1 + 3 * μ 2 + 3 * μ 3
  map_add' μ ν := by simp only [Pi.add_apply]; ring
  map_smul' c μ := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private def modelRootWeight (r : TypeDRootIndex 4) : Weight :=
  fun i => (typeDRootPairing 2).pairingIn ℤ r (typeDSimpleRootIndex 2 i)

private theorem weightHeight_simple (i : Fin 4) :
    weightHeight (modelRootWeight (typeDSimpleRootIndex 2 i)) = 1 := by
  have hp (j : Fin 4) : modelRootWeight (typeDSimpleRootIndex 2 i) j =
      typeDCartanMatrix 2 i j := by
    simpa only [modelRootWeight, RootPairing.Base.cartanMatrixIn_def, typeDRootPairing_baseEquiv_val]
      using typeDRootPairing_base_cartanMatrix 2 i j
  simp only [weightHeight, LinearMap.coe_mk, AddHom.coe_mk, hp]
  fin_cases i <;> norm_num [typeDCartanMatrix] <;> decide

private theorem weightHeight_modelRoot (r : TypeDRootIndex 4) :
    weightHeight (modelRootWeight r) = (typeDRootPairing_base 2).height r := by
  let L : (typeDRootPairing 2).rootSpan ℤ →ₗ[ℤ] ℤ :=
    weightHeight.comp (LinearMap.pi fun i : Fin 4 =>
      (typeDRootPairing 2).coroot'In ℤ (typeDSimpleRootIndex 2 i))
  have hL (s : TypeDRootIndex 4) :
      L ((typeDRootPairing 2).rootSpanMem ℤ s) = weightHeight (modelRootWeight s) := by
    change weightHeight _ = weightHeight _
    congr 1
  have hLs (s : (typeDRootPairing_base 2).support) :
      L ((typeDRootPairing 2).rootSpanMem ℤ s) = 1 := by
    rw [hL, ← (typeDRootPairing_baseEquiv 2).apply_symm_apply s]
    exact weightHeight_simple _
  obtain ⟨f, _, _, hf⟩ := (typeDRootPairing_base 2).exists_root_eq_sum_int r
  have hspan : (typeDRootPairing 2).rootSpanMem ℤ r =
      ∑ s ∈ (typeDRootPairing_base 2).support,
        f s • (typeDRootPairing 2).rootSpanMem ℤ s := by
    apply Subtype.ext
    simpa using hf
  rw [← hL, hspan, map_sum, (typeDRootPairing_base 2).height_eq_sum hf]
  apply Finset.sum_congr rfl
  intro s hs
  rw [map_smul, hLs ⟨s, hs⟩]
  simp

omit [IsAlgClosed k] in
/-- The coordinate functional is the unchanged root system height. -/
theorem weightHeight_root (S : D4Geometry K) (α : S.roots.Root) :
    weightHeight (rootWeight S α) = S.roots.height α := by
  have hcoord : rootWeight S α = modelRootWeight (S.rootEquiv α) := by
    funext i
    apply Int.cast_injective (α := ℝ)
    rw [show (rootWeight S α i : ℝ) =
      (typeDRootPairing 2).pairing (S.rootEquiv α) (typeDSimpleRootIndex 2 i) by
      simpa only [rootWeight, Equiv.apply_symm_apply] using
        S.based.1 α (S.rootEquiv.symm (typeDSimpleRootIndex 2 i))]
    exact ((typeDRootPairing 2).algebraMap_pairingIn ℤ _ _).symm
  rw [hcoord, weightHeight_modelRoot]
  exact (S.based.2.2.2.2 α).symm

/-- A scaled root-group intertwiner induces the corresponding first-coefficient intertwiner. -/
theorem rootOperator_intertwine (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (r s : S.roots.Root) (A D : Module.End k V) (c : k)
    (h : ∀ (t : k) (v : V),
      A ((ρ.action (S.chevalley.x r t)).val v) =
        (ρ.action (S.chevalley.x s (c * t))).val (D v)) :
    A * rootOperator S ρ hρ r = c • (rootOperator S ρ hρ s * D) := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext i
  let l := (Module.finBasis k V).coord i
  have hp : curvePolynomial ρ hρ (rootMorphism S r) (l.comp A) v =
      (curvePolynomial ρ hρ (rootMorphism S s) l (D v)).comp
        (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [curvePolynomial_eval, rootMorphism_apply, Polynomial.eval_comp,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply, h]
  have hc := congrArg (fun p : Polynomial k => p.coeff 1) hp
  rw [← dual_curveOperator, Polynomial.comp_C_mul_X_coeff, pow_one,
    ← dual_curveOperator] at hc
  change l (A (rootOperator S ρ hρ r v)) = l (c • rootOperator S ρ hρ s (D v))
  simpa only [LinearMap.comp_apply, map_smul, smul_eq_mul, mul_comm, rootOperator] using hc

omit [IsAlgClosed k] in
private theorem pointCharacter_mul (T : Variety k) [AlgebraicGroup T]
    (χ ψ : TorusCharacter T) (t : Variety.Point T) :
    (χ * ψ).pointCharacter t = χ.pointCharacter t * ψ.pointCharacter t := rfl

/-- The actual first coefficient shifts the full integral left weight. -/
theorem rootOperator_mem_integralWeightSpace (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) {μ : Weight} {v : V}
    (hv : v ∈ integralWeightSpace S ρ μ) :
    rootOperator S ρ hρ α v ∈ integralWeightSpace S ρ (μ + rootWeight S α) := by
  intro t
  let A : Module.End k V := (ρ.action (S.torus.includePoint t)).val
  let c := ((S.roots.rootWeight α)⁻¹).pointCharacter t
  have he := rootOperator_intertwine S ρ hρ α α A A c (by
    intro a w
    have hg := LeftWeights.direct_conjugation (S.realized.2.2.1 α).2
      (S.rootParam α) a t
    simp only [S.rootParam_spec] at hg
    have hh : S.torus.includePoint t * S.chevalley.x α a =
        S.chevalley.x α (c * a) * S.torus.includePoint t := by
      rw [← hg]
      group
    have h := congrArg (fun g => (ρ.action g).val w) hh
    simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A] using h)
  have he' := congrArg (fun L : Module.End k V => L v) he
  have ht := hv t
  change A v = _ at ht
  change A (rootOperator S ρ hρ α v) = c • rootOperator S ρ hρ α (A v) at he'
  rw [ht, map_smul, smul_smul] at he'
  rw [S.leftWeightEmbedding_add, pointCharacter_mul, rootWeight_character]
  change A (rootOperator S ρ hρ α v) =
    ((S.leftWeightEmbedding μ).pointCharacter t * c) • rootOperator S ρ hρ α v
  rw [mul_comm c] at he'
  exact he'

/-- An operator word shifts the weight by the sum of its root weights. -/
theorem word_mem_integralWeightSpace (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (l : List S.roots.Root) {μ : Weight} {v : V}
    (hv : v ∈ integralWeightSpace S ρ μ) :
    (l.map (rootOperator S ρ hρ)).prod v ∈
      integralWeightSpace S ρ (μ + (l.map (rootWeight S)).sum) := by
  induction l with
  | nil => simpa using hv
  | cons r l ih =>
    simpa [add_assoc, add_comm, add_left_comm] using
      rootOperator_mem_integralWeightSpace S ρ hρ r ih

/-- Negative cyclicity from a torus weight vector gives a spanning weight decomposition. -/
theorem integralWeightSpace_iSup_eq_top_of_negative_span (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {μ : Weight} {v : V} (hv : v ∈ integralWeightSpace S ρ μ)
    (hspan : negativeRootSpan S ρ hρ v = ⊤) :
    (⨆ ν : Weight, integralWeightSpace S ρ ν) = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, rfl⟩
  have h := word_mem_integralWeightSpace S ρ hρ (l.map fun α => S.roots.neg α.val) hv
  exact Submodule.mem_iSup_of_mem _
    (by simpa only [List.map_map, Function.comp_def] using h)

end PositivePrimitivesLeft
open PositivePrimitivesLeft

/-- Every sufficiently long positive word vanishes, with one bound for all words. -/
theorem hasNilpotentPositiveAction_of_negative_span (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {μ : Weight} {v : V} (hv : v ∈ integralWeightSpace S ρ μ)
    (hspan : negativeRootSpan S ρ hρ v = ⊤) : HasNilpotentPositiveAction S ρ hρ := by
  classical
  let H := weightHeight
  have hfinite := Submodule.finite_ne_bot_of_iSupIndep (integralWeightSpace_iSupIndep S ρ)
  obtain ⟨hi, hhi⟩ := (hfinite.image H).bddAbove
  obtain ⟨lo, hlo⟩ := (hfinite.image H).bddBelow
  refine ⟨(hi - lo).toNat + 1, ?_⟩
  intro l hl
  have hheight : (l.length : ℤ) ≤ H ((l.map fun r => rootWeight S r.val).sum) := by
    clear hl
    induction l with
    | nil => simp [H]
    | cons r l ih =>
      have hr : 0 < H (rootWeight S r.val) := by
        rw [weightHeight_root]
        simpa only [S.realized.2.2.2.2.2.2.2.2.2.2.1, Set.mem_ofPred_eq] using r.property
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
        List.sum_cons, map_add]
      omega
  ext x
  have hx : x ∈ ⨆ ν, integralWeightSpace S ρ ν := by
    rw [integralWeightSpace_iSup_eq_top_of_negative_span S ρ hρ hv hspan]
    trivial
  change (l.map fun r => rootOperator S ρ hρ r.val).prod x = 0
  refine Submodule.iSup_induction (integralWeightSpace S ρ)
    (motive := fun y => (l.map fun r => rootOperator S ρ hρ r.val).prod y = 0) hx ?_ ?_ ?_
  · intro ν y hy
    by_contra hne
    have hy0 : y ≠ 0 := by intro hz; apply hne; simp [hz]
    have hν : integralWeightSpace S ρ ν ≠ ⊥ := by
      intro hz
      exact hy0 (by simpa [hz] using hy)
    have hword := word_mem_integralWeightSpace S ρ hρ (l.map Subtype.val) hy
    have hν' : integralWeightSpace S ρ
        (ν + (l.map fun r => rootWeight S r.val).sum) ≠ ⊥ := by
      intro hz
      apply hne
      simpa only [List.map_map, Function.comp_def, hz, Submodule.mem_bot] using hword
    have hb := hhi ⟨_, hν', rfl⟩
    have ha := hlo ⟨ν, hν, rfl⟩
    simp only [map_add] at hb
    rw [hl] at hheight
    have hn := Int.self_le_toNat (hi - lo)
    omega
  · simp
  · intro y z hy hz
    simp only [map_add, hy, hz, add_zero]

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
