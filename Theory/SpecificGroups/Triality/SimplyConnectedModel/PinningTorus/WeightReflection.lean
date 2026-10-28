module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration.Weyl
public import Theory.AlgebraicGroup.RootSystems.TypeD4RestrictedWeights
public import Theory.AlgebraicGroup.Tori.Character.Tuple

/-!
# The pinned Spin normalizers on integral torus weights

The inverse conjugation by each source simple normalizer is a regular
involutory automorphism of the actual Spin coroot torus. In simple-coroot
coordinates its Laurent matrix is the transpose of the integral weight
reflection. The point identity follows by conjugating each factor in the
ordered coroot product; the character identity follows by multiplying its
Laurent monomials.

`torusReflection_conjugation` and `weightEmbedding_reflection` are precisely
the conjugation and character inputs of `RestrictedWeights`, with
`g i = Pinning.simpleNormalizer k i` and
`c i = (CorootTorus.torusReflection k i).onPoints`. This uses the source's
inverse conjugation and the raw coroot coordinates throughout.

Source: GLS3, Theorem 1.12.1(e,h–k) and Proposition 1.14.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
noncomputable section
namespace Triality.SimplyConnected.Pinning.CorootTorus
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def reflectionMatrix (i j l : Fin 4) : ℤ :=
  (if j = l then 1 else 0) - if j = i then typeDCartanMatrix 2 i l else 0

private theorem cartan_symm (i j : Fin 4) :
    typeDCartanMatrix 2 i j = typeDCartanMatrix 2 j i := by
  fin_cases i <;> fin_cases j <;> decide

private def reflectedParameters (i : Fin 4) (t : Fin 4 → kˣ) : Fin 4 → kˣ :=
  fun j => ∏ l, t l ^ reflectionMatrix i j l

omit [IsAlgClosed k] [CharP k 2] in
private theorem reflectedParameters_prod (i : Fin 4) (t : Fin 4 → kˣ) :
    reflectedParameters k i t =
      (List.ofFn fun j : Fin 4 => Pi.mulSingle j (t j) *
        Pi.mulSingle i (t j ^ (-typeDCartanMatrix 2 j i))).prod := by
  funext l
  rw [List.prod_ofFn, Finset.prod_apply]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Pi.mul_apply]
  by_cases hlj : l = j <;> by_cases hli : l = i <;>
    simp_all [reflectionMatrix, zpow_sub, cartan_symm]

/-- The regular inverse conjugation on the Spin torus, in simple-coroot coordinates. -/
def torusReflection (i : Fin 4) :
    AlgebraicGroup.Morphism (closedSubgroup k).carrierVariety
      (closedSubgroup k).carrierVariety :=
  (coordinateIso k).hom.comp
    ((dCharacterTupleMorphism 4 4 (reflectionMatrix i)).comp (coordinateIso k).inv)

private theorem torusReflection_parameter (i : Fin 4) (t : Fin 4 → kˣ) :
    (torusReflection k i).onPoints (parameterPoint k t) =
      parameterPoint k (reflectedParameters k i t) := by
  change (coordinateIso k).hom.onPoints
    ((dCharacterTupleMorphism 4 4 (reflectionMatrix i)).onPoints
      ((coordinateIso k).inv.onPoints (parameterPoint k t))) = _
  rw [coordinateIso_inv_parameter, coordinateIso_hom_apply]
  congr 1
  funext j
  rw [dCharacterTupleMorphism_apply, Equiv.apply_symm_apply]
  rfl

private theorem parameter_mulSingle (i : Fin 4) (t : kˣ) :
    parameter k (Pi.mulSingle i t) = simpleCoroot k i t := by
  exact parameter_single k i t

private theorem parameter_reflection (i : Fin 4) (t : Fin 4 → kˣ) :
    parameter k (reflectedParameters k i t) =
      (simpleNormalizer k i)⁻¹ * parameter k t * simpleNormalizer k i := by
  let f := MulAut.conj ((simpleNormalizer k i)⁻¹)
  have hj (j : Fin 4) :
      parameter k (Pi.mulSingle j (t j) *
          Pi.mulSingle i (t j ^ (-typeDCartanMatrix 2 j i))) =
        f (simpleCoroot k j (t j)) := by
    rw [parameter_mul, parameter_mulSingle, parameter_mulSingle]
    simpa only [f, MulAut.conj_apply, inv_inv] using
      (simpleNormalizer_simpleCoroot_conjugation k i j (t j)).symm
  have h : parameter k (reflectedParameters k i t) = f (parameter k t) := by
    rw [reflectedParameters_prod]
    change pointHom k _ = f (parameter k t)
    rw [map_list_prod, parameter, map_list_prod]
    simp only [List.map_ofFn]
    congr 2
    funext j
    exact hj j
  simpa only [f, MulAut.conj_apply, inv_inv] using h

/-- The Laurent morphism is conjugation by the same pinned simple normalizer. -/
theorem torusReflection_inclusion (i : Fin 4)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (closedSubgroup k).includePoint ((torusReflection k i).onPoints t) =
      (simpleNormalizer k i)⁻¹ * (closedSubgroup k).includePoint t * simpleNormalizer k i := by
  obtain ⟨x, rfl⟩ := (coordinateIso k).toMulEquiv.surjective t
  change (closedSubgroup k).inclusion.onPoints
      ((torusReflection k i).onPoints ((coordinateIso k).hom.onPoints x)) =
    (simpleNormalizer k i)⁻¹ * (closedSubgroup k).inclusion.onPoints
      ((coordinateIso k).hom.onPoints x) * simpleNormalizer k i
  rw [coordinateIso_hom_apply, torusReflection_parameter, inclusion_parameterPoint,
    inclusion_parameterPoint, parameter_reflection]

/-- The multiplication order required for transporting left-action weight spaces. -/
theorem torusReflection_conjugation (i : Fin 4)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (closedSubgroup k).includePoint t * simpleNormalizer k i =
      simpleNormalizer k i * (closedSubgroup k).includePoint ((torusReflection k i).onPoints t) := by
  rw [torusReflection_inclusion]
  group

private theorem reflectionMatrix_weight (i : Fin 4) (a : Fin 4 → ℤ) (l : Fin 4) :
    (∑ j, a j * reflectionMatrix i j l) = D4RestrictedWeight.reflection i a l := by
  simp only [reflectionMatrix, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
  simp [D4RestrictedWeight.reflection]

/-- Integral character reflection for the genuine algebraic weight embedding. -/
theorem weightEmbedding_reflection (i : Fin 4) (a : Fin 4 → ℤ)
    (t : Variety.Point (closedSubgroup k).carrierVariety) :
    (weightEmbedding k (D4RestrictedWeight.reflection i a)).pointCharacter t =
      (weightEmbedding k a).pointCharacter ((torusReflection k i).onPoints t) := by
  obtain ⟨x, rfl⟩ := (coordinateIso k).toMulEquiv.surjective t
  change (weightEmbedding k (D4RestrictedWeight.reflection i a)).pointCharacter
      ((coordinateIso k).hom.onPoints x) =
    (weightEmbedding k a).pointCharacter
      ((torusReflection k i).onPoints ((coordinateIso k).hom.onPoints x))
  rw [coordinateIso_hom_apply, torusReflection_parameter, weightEmbedding_parameter,
    weightEmbedding_parameter]
  have hu : (∏ l, (dPointEquiv 4 x l) ^ D4RestrictedWeight.reflection i a l) =
      ∏ j, (reflectedParameters k i (dPointEquiv 4 x) j) ^ a j := by
    simp only [reflectedParameters]
    rw [prod_laurentMonomial_zpow]
    simp only [reflectionMatrix_weight]
  simpa using congrArg (fun z : kˣ => (z : k)) hu

/-- Each torus reflection has square the identity, including in characteristic two. -/
theorem torusReflection_involutive (i : Fin 4) :
    Function.Involutive (torusReflection k i).onPoints := by
  intro t
  apply (closedSubgroup k).inclusion_injective
  change (closedSubgroup k).includePoint
    ((torusReflection k i).onPoints ((torusReflection k i).onPoints t)) =
      (closedSubgroup k).includePoint t
  rw [torusReflection_inclusion, torusReflection_inclusion]
  have hi : (simpleNormalizer k i)⁻¹ = simpleNormalizer k i := normalizerWord_inv k _ _
  have hsq : simpleNormalizer k i * simpleNormalizer k i = 1 := by
    rw [← pow_two]
    exact normalizerWord_sq k _ _
  calc
    _ = (simpleNormalizer k i * simpleNormalizer k i) *
        (closedSubgroup k).includePoint t * (simpleNormalizer k i * simpleNormalizer k i) := by
      rw [hi]
      group
    _ = _ := by rw [hsq, one_mul, mul_one]

/-- The reflection is an algebraic automorphism, with itself as regular inverse. -/
@[expose] def torusReflectionIso (i : Fin 4) :
    AlgebraicGroup.Iso (closedSubgroup k).carrierVariety (closedSubgroup k).carrierVariety where
  hom := torusReflection k i
  inv := torusReflection k i
  hom_inv_id := torusReflection_involutive k i
  inv_hom_id := torusReflection_involutive k i

/-- The pinned simple normalizer belongs to the actual torus normalizer. -/
theorem simpleNormalizer_mem_torusNormalizer (i : Fin 4) :
    simpleNormalizer k i ∈ Subgroup.normalizer ((closedSubgroup k).toSubgroup : Set (Points k)) := by
  have hc (x : Points k) (hx : x ∈ (closedSubgroup k).toSubgroup) :
      (simpleNormalizer k i)⁻¹ * x * simpleNormalizer k i ∈
        (closedSubgroup k).toSubgroup := by
    obtain ⟨t, rfl⟩ := (mem_iff_parameter k x).mp hx
    rw [← parameter_reflection]
    exact parameter_mem k _
  apply Subgroup.mem_normalizer_iff''.mpr
  intro x
  refine ⟨hc x, fun hx => ?_⟩
  have h := hc _ hx
  have hi : (simpleNormalizer k i)⁻¹ = simpleNormalizer k i := normalizerWord_inv k _ _
  have hsq : simpleNormalizer k i * simpleNormalizer k i = 1 := by
    rw [← pow_two]
    exact normalizerWord_sq k _ _
  have he : (simpleNormalizer k i)⁻¹ *
      ((simpleNormalizer k i)⁻¹ * x * simpleNormalizer k i) * simpleNormalizer k i = x := by
    calc
      _ = (simpleNormalizer k i * simpleNormalizer k i) * x *
          (simpleNormalizer k i * simpleNormalizer k i) := by rw [hi]; group
      _ = x := by rw [hsq, one_mul, mul_one]
  rwa [he] at h

end Triality.SimplyConnected.Pinning.CorootTorus
