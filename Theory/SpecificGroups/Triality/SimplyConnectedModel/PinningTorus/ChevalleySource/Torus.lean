module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.CharacterLattice

/-!
# The torus clauses for the concrete Spin D4 Chevalley system

The standard-base support product is the actual coroot-coordinate map of the
closed Spin torus. Integral root coefficients expand each coroot both in the
real root pairing and in this product. Injectivity of the coordinate map gives
the product kernel. Twice the inverse D4 Cartan matrix then reduces the kernel
of its root monomials to square roots of one, trivial in characteristic two.
The genuine fundamental algebraic characters generate the root characters and
have Kronecker pairings with the same source simple-coroot words.

These results use the original Clifford-model points and the literal standard
D4 base, with no Chevalley-system, adjointness or universality premise.
Source: GLS3, 1.12.1(e--g), 1.12.5(b,c), and 1.14.1--2
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
noncomputable section
namespace Triality.SimplyConnected.Pinning.ChevalleySource.Torus
abbrev Support := (typeDRootPairing_base 2).support
abbrev supportEquiv : Fin 4 ≃ Support := typeDRootPairing_baseEquiv 2
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The literal source-support product has exactly the published coroot coordinates. -/
theorem supportCorootProduct_eq_parameter (t : Support → kˣ) :
    (Support.attach.toList.map fun i : Support => corootWord k i.val (t i)).prod =
      CorootTorus.parameter k (fun j => t (supportEquiv j)) := by
  classical
  have hs (i : Support) : corootWord k i.val (t i) =
      (CorootTorus.pointHom k) (Function.update (fun _ => 1) (supportEquiv.symm i) (t i)) := by
    change _ = CorootTorus.parameter k _
    rw [CorootTorus.parameter_single]
    congr 1
    exact (congrArg Subtype.val (supportEquiv.apply_symm_apply i)).symm
  simp_rw [hs]
  have hm := map_list_prod (CorootTorus.pointHom k)
    (Support.attach.toList.map fun i : Support => Function.update (fun _ => 1) (supportEquiv.symm i) (t i))
  simp only [List.map_map, Function.comp_def] at hm
  rw [← hm, Finset.prod_map_toList]
  apply congrArg (CorootTorus.parameter k)
  funext j
  simp only [Finset.prod_apply]
  rw [Finset.prod_eq_single (supportEquiv j)]
  · simp
  · intro i hi hij
    have h : j ≠ supportEquiv.symm i := by
      intro h
      apply hij
      exact (supportEquiv.apply_symm_apply i).symm.trans (congrArg supportEquiv h.symm)
    simp [Function.update_of_ne h]
  · simp

/-- A product of actual simple coroots is trivial exactly at the identity tuple. -/
theorem supportCorootProduct_eq_one_iff (t : Support → kˣ) :
    (Support.attach.toList.map fun i : Support => corootWord k i.val (t i)).prod = 1 ↔
      ∀ i, t i = 1 := by
  rw [supportCorootProduct_eq_parameter]
  constructor
  · intro h i
    have he := CorootTorus.parameter_injective k (h.trans (CorootTorus.parameter_one k).symm)
    simpa using congrFun he (supportEquiv.symm i)
  · intro h
    have he : (fun j => t (supportEquiv j)) = 1 := funext fun i => h _
    rw [he, CorootTorus.parameter_one]

/-- Every source coroot word has the integral simple-coroot coordinates. -/
theorem corootWord_eq_parameter (r : RootIndex) (t : kˣ) :
    corootWord k r t = CorootTorus.parameter k (fun i => t ^ rootCorootCoefficients r i) := by
  let z : Variety.Point (KMult k) := (dPointEquiv 1).symm (fun _ => t)
  have h := coordinateRootCocharacter_inclusion k (CorootTorus.closedSubgroup k)
    (CorootTorus.coordinateIso k) (hasCorootCoordinates k) r z
  change (CorootTorus.closedSubgroup k).inclusion.onPoints
    ((CorootTorus.coordinateIso k).hom.onPoints
      ((dCharacterTupleMorphism 4 1 (fun i _ => rootCorootCoefficients r i)).onPoints z)) = _ at h
  rw [hasCorootCoordinates k] at h
  have hd : dPointEquiv 4
      ((dCharacterTupleMorphism (k := k) 4 1 (fun i _ => rootCorootCoefficients r i)).onPoints z) =
      fun i => t ^ rootCorootCoefficients r i := by
    funext i
    rw [dCharacterTupleMorphism_apply]
    simp only [Fin.prod_univ_one, z, Equiv.apply_symm_apply]
  rw [hd] at h
  simpa only [z, Equiv.apply_symm_apply, corootTuplePoint, CorootTorus.parameter] using h.symm

/-- The integral source coefficients expand the actual D4 coroots. -/
theorem coroot_expansion_fin (r : RootIndex) :
    (typeDRootPairing 2).coroot r =
      ∑ i : Fin 4, rootCorootCoefficients r i • (typeDRootPairing 2).coroot (simpleRoot i) := by
  change typeDRootFunctional 4 r =
    ∑ i : Fin 4, rootCorootCoefficients r i • typeDRootFunctional 4 (simpleRoot i)
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, typeDRootFunctional_apply,
    zsmul_eq_mul, dot, typeDCorootVector]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have he := congrArg (fun z : ℤ => (z : ℝ)) (rootCorootCoefficients_expansion r p)
  simp only [Int.cast_sum, Int.cast_mul, evenOrthogonalRootExponent_cast] at he
  have he' : (typeDRootEmbedding 4 r : Vec 4) p =
      ∑ i : Fin 4, (rootCorootCoefficients r i : ℝ) *
        (typeDRootEmbedding 4 (simpleRoot i) : Vec 4) p := by
    simp only [mul_neg, Finset.sum_neg_distrib] at he
    exact (neg_injective he).symm
  rw [he', Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Integral weight coordinates are the literal root-datum weight pairings. -/
theorem weightPairing_simple (a : Fin 4 → ℤ) (i : Fin 4) :
    (pinnedRootData k).weightPairing (CorootTorus.weightEmbedding k a)
      (pinnedRootIndex k (simpleRoot i)) = a i := by
  apply (weightCocharacterEquation_existsUnique (CorootTorus.closedSubgroup k)
    (CorootTorus.weightEmbedding k a)
    ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i)))).unique
  · exact (pinnedRootData_isRealization k).weightPairing_spec _ _
  · exact pinnedRootData_weight_simpleCoroot k a i

/-- A coordinate weight is the corresponding actual fundamental character. -/
theorem weightEmbedding_single (i : Fin 4) :
    CorootTorus.weightEmbedding k (Pi.single i (1 : ℤ)) =
      CorootTorus.fundamentalCharacter k i := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  change (CorootTorus.weightEmbedding k (Pi.single i (1 : ℤ))).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x) =
    (CorootTorus.fundamentalCharacter k i).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x)
  rw [CorootTorus.coordinateIso_hom_apply, CorootTorus.weightEmbedding_parameter,
    CorootTorus.fundamentalCharacter_parameter]
  classical
  simp [Pi.single_apply]

/-- Every integral torus weight is a product of the genuine fundamental characters. -/
theorem weightEmbedding_eq_prod (a : Fin 4 → ℤ) :
    CorootTorus.weightEmbedding k a =
      ∏ i, CorootTorus.fundamentalCharacter k i ^ a i := by
  apply Additive.ofMul.injective
  have he : a = ∑ i : Fin 4, a i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Pi.single_apply]
  rw [← characterLatticeEquiv_apply]
  conv_lhs => rw [he, map_sum]
  simp only [map_zsmul, characterLatticeEquiv_apply, weightEmbedding_single,
    ofMul_prod, ofMul_zpow]

/-- Fundamental characters and simple coroots have Kronecker pairing. -/
theorem fundamentalCharacter_weightPairing (i j : Fin 4) :
    (pinnedRootData k).weightPairing (CorootTorus.fundamentalCharacter k i)
      (pinnedRootIndex k (simpleRoot j)) = if j = i then 1 else 0 := by
  rw [← weightEmbedding_single, weightPairing_simple]
  simp [Pi.single_apply, eq_comm]

omit [IsAlgClosed k] in
/-- In characteristic two the D4 Cartan monomials have trivial kernel on units. -/
theorem cartan_kernel (t : Fin 4 → kˣ)
    (ht : ∀ j : Fin 4, (∏ i, t i ^ typeDCartanMatrix 2 j i) = 1) :
    ∀ i, t i = 1 := by
  let ev : (Fin 4 → ℤ) →+ Additive kˣ :=
    { toFun a := Additive.ofMul (∏ i, t i ^ a i)
      map_zero' := by simp
      map_add' a b := by
        change (∏ i, t i ^ (a i + b i)) = _
        simp only [zpow_add, Finset.prod_mul_distrib]
        rfl }
  have hzero (j : Fin 4) : ev (typeDCartanMatrix 2 j) = 0 := ht j
  intro i
  have he := congrArg ev (two_smul_eq_cartan_combination (Pi.single i 1))
  simp only [map_zsmul, map_sum, hzero, smul_zero, Finset.sum_const_zero] at he
  have hei : ev (Pi.single i 1) = Additive.ofMul (t i) := by
    change Additive.ofMul (∏ j : Fin 4, t j ^ ((Pi.single i (1 : ℤ) : Fin 4 → ℤ) j)) = Additive.ofMul (t i)
    simp [Pi.single_apply]
  rw [hei] at he
  have hs : t i ^ 2 = (1 : kˣ) ^ 2 := by
    change t i ^ (2 : ℤ) = 1 at he
    simpa only [zpow_ofNat, one_pow] using he
  apply Units.ext
  apply CharTwo.sq_injective
  exact congrArg Units.val hs


/-- Integral simple-coroot coefficients in the literal standard-base support. -/
def coefficients (r : RootIndex) (i : Support) : ℤ :=
  rootCorootCoefficients r (supportEquiv.symm i)

/-- Integral coroot expansion indexed by the actual standard-base support. -/
theorem coroot_expansion (r : RootIndex) :
    (typeDRootPairing 2).coroot r =
      ∑ i : Support, coefficients r i • (typeDRootPairing 2).coroot i := by
  rw [← supportEquiv.sum_comp]
  simpa only [coefficients, Equiv.symm_apply_apply, typeDRootPairing_baseEquiv_val]
    using coroot_expansion_fin r

/-- The same coefficients expand the actual coroot words in the source ordering. -/
theorem corootWord_expansion (r : RootIndex) (t : kˣ) :
    corootWord k r t =
      (Support.attach.toList.map fun i : Support =>
        corootWord k i.val (t ^ coefficients r i)).prod := by
  rw [supportCorootProduct_eq_parameter, corootWord_eq_parameter]
  simp only [coefficients, Equiv.symm_apply_apply]

/-- The root-monomial kernel clause holds on the actual Spin model. -/
theorem supportCorootProduct_eq_one_iff_cartan (t : Support → kˣ) :
    (Support.attach.toList.map fun i : Support => corootWord k i.val (t i)).prod = 1 ↔
      ∀ j : Support, (∏ i : Support, t i ^ (pinnedRootData k).pairing
        (Equiv.ulift.symm j.val) (Equiv.ulift.symm i.val)) = 1 := by
  rw [supportCorootProduct_eq_one_iff]
  constructor
  · intro h j
    simp only [h, one_zpow, Finset.prod_const_one]
  · intro h j
    have ht (l : Fin 4) : (∏ i : Fin 4,
        t (supportEquiv i) ^ typeDCartanMatrix 2 l i) = 1 := by
      have hl := h (supportEquiv l)
      rw [← supportEquiv.prod_comp] at hl
      change (∏ i : Fin 4, t (supportEquiv i) ^ (pinnedRootData k).pairing
        (pinnedRootIndex k (simpleRoot l)) (pinnedRootIndex k (simpleRoot i))) = 1 at hl
      simpa only [pinnedRootData_pairing_simple] using hl
    simpa only [Equiv.apply_symm_apply] using cartan_kernel k (fun i => t (supportEquiv i)) ht
      (supportEquiv.symm j)

/-- The literal Chevalley adjoint clause tests all roots, and has the same kernel. -/
theorem supportCorootProduct_eq_one_iff_roots (t : Support → kˣ) :
    (Support.attach.toList.map fun i : Support => corootWord k i.val (t i)).prod = 1 ↔
      ∀ j : RootIndex, (∏ i : Support, t i ^ (pinnedRootData k).pairing
        (Equiv.ulift.symm j) (Equiv.ulift.symm i.val)) = 1 := by
  constructor
  · intro h j
    have ht := (supportCorootProduct_eq_one_iff k t).mp h
    simp only [ht, one_zpow, Finset.prod_const_one]
  · intro h
    exact (supportCorootProduct_eq_one_iff_cartan k t).mpr (fun j => h j.val)

/-- The genuine fundamental algebraic characters, indexed by the source base. -/
def weights (i : Support) : TorusWeight (CorootTorus.closedSubgroup k) :=
  CorootTorus.fundamentalCharacter k (supportEquiv.symm i)

/-- The source-indexed fundamental characters generate every actual root character. -/
theorem weights_generate : Set.range (pinnedRootData k).rootWeight ⊆
    Subgroup.closure (Set.range (weights k)) := by
  rintro χ ⟨r, rfl⟩
  rw [pinnedRootData_rootWeight, weightEmbedding_eq_prod]
  apply Subgroup.prod_mem
  intro i _
  apply Subgroup.zpow_mem
  apply Subgroup.subset_closure
  exact ⟨supportEquiv i, by simp only [weights, Equiv.symm_apply_apply]⟩

/-- Source-indexed fundamental characters retain the Kronecker pairing. -/
theorem weights_pairing (j i : Support) :
    (pinnedRootData k).weightPairing (weights k j) (Equiv.ulift.symm i.val) =
      if i = j then 1 else 0 := by
  obtain ⟨j, rfl⟩ := supportEquiv.surjective j
  obtain ⟨i, rfl⟩ := supportEquiv.surjective i
  simp only [weights, Equiv.symm_apply_apply, supportEquiv.injective.eq_iff]
  exact fundamentalCharacter_weightPairing k j i

/-- The fundamental-weight monomials detect the actual coroot-product kernel. -/
theorem supportCorootProduct_eq_one_iff_weights (t : Support → kˣ) :
    (Support.attach.toList.map fun i : Support => corootWord k i.val (t i)).prod = 1 ↔
      ∀ j : Support, (∏ i : Support, t i ^ (pinnedRootData k).weightPairing
        (weights k j) (Equiv.ulift.symm i.val)) = 1 := by
  classical
  rw [supportCorootProduct_eq_one_iff]
  simp only [weights_pairing, apply_ite, zpow_one, zpow_zero,
    Finset.prod_ite_eq', Finset.mem_univ, if_true]

end Triality.SimplyConnected.Pinning.ChevalleySource.Torus
