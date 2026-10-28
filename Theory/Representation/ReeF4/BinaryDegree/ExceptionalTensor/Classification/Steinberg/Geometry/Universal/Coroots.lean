module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.Characters
public import Theory.AlgebraicGroup.Tori.IsoOfCharacterPullbackSurjective
public import Theory.AlgebraicGroup.Tori.Characters.ProperImage

/-!
# The product of the four actual F4 coroots

The coroot product is a regular algebraic-group morphism from the rank-four
diagonal torus to the model's actual maximal torus. Its character pullback is
exactly evaluation on the four coroots. The F4 root-lattice calculation proves
that pullback is surjective, so the morphism has no inseparability defect.

If the four coroots also separate characters, the product is surjective on
points: a proper torus image would be annihilated by a nontrivial character.
The torus character criterion then supplies an algebraic isomorphism. This
proves the torus part of GLS3, Theorem 1.12.5(b), with character separation
explicit; whole-group universality is a separate isogeny argument.
-/

public section

open Theory.AlgebraicGroup.StandardRootSystem

universe u

namespace Theory.AlgebraicGroup.RootSystemModel

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private def oneMorphism (S T : Variety k) [AlgebraicGroup S] [AlgebraicGroup T] :
    Morphism S T where
  toVariety := Variety.Morphism.const S T 1
  map_one := rfl
  map_mul := by intro _ _; exact (one_mul 1).symm

private def mulMorphism {S T : Variety k} [AlgebraicGroup S] [AlgebraicGroup T]
    (hT : IsMulCommutative (Variety.Point T)) (f g : Morphism S T) : Morphism S T where
  toVariety := (Theory.AlgebraicGroup.mulMorphism T).comp (f.toVariety.pair g.toVariety)
  map_one := by change f.onPoints 1 * g.onPoints 1 = 1; simp
  map_mul := by
    intro x y
    change f.onPoints (x * y) * g.onPoints (x * y) =
      (f.onPoints x * g.onPoints x) * (f.onPoints y * g.onPoints y)
    rw [map_mul, map_mul]
    have hc : f.onPoints y * g.onPoints x = g.onPoints x * f.onPoints y :=
      (isMulCommutative_iff.mp hT) _ _
    simp only [mul_assoc, ← mul_assoc (f.onPoints y), hc]

private def listProduct {S T : Variety k} [AlgebraicGroup S] [AlgebraicGroup T]
    (hT : IsMulCommutative (Variety.Point T)) : List (Morphism S T) → Morphism S T
  | [] => oneMorphism S T
  | f :: fs => mulMorphism hT f (listProduct hT fs)

omit [IsAlgClosed k] in
private lemma listProduct_apply {S T : Variety k} [AlgebraicGroup S] [AlgebraicGroup T]
    (hT : IsMulCommutative (Variety.Point T)) (fs : List (Morphism S T))
    (x : Variety.Point S) :
    (listProduct hT fs).onPoints x = (fs.map fun f => f.onPoints x).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.onPoints x * (listProduct hT fs).onPoints x = _
    rw [ih]
    rfl

/-- The algebraic product morphism of the four actual coroots in standard F4 order. -/
noncomputable def f4CorootProduct (M : RootSystemModel typeF4RootPairingULift G) :
    Morphism (dVariety k 4) M.torus.carrierVariety :=
  listProduct M.maximalTorus.1.isMulCommutative
    (List.ofFn fun i =>
      (M.rootData.rootCocharacter (f4SimpleRoot M i)).comp (dCoordinateCharacter 4 i))

omit [IsAlgClosed k] in
theorem f4CorootProduct_apply (M : RootSystemModel typeF4RootPairingULift G)
    (x : Variety.Point (dVariety k 4)) :
    (f4CorootProduct M).onPoints x =
      (List.ofFn fun i => (M.rootData.rootCocharacter (f4SimpleRoot M i)).onPoints
        ((dCoordinateCharacter 4 i).onPoints x)).prod := by
  rw [f4CorootProduct, listProduct_apply, List.map_ofFn]
  rfl

/-- Character pullback along the product has the four coroot pairings as its exponents. -/
theorem f4CorootProduct_pullback (M : RootSystemModel typeF4RootPairingULift G)
    (χ : TorusWeight M.torus) :
    TorusCharacter.pullback (f4CorootProduct M) χ =
      dLaurentCharacter 4 (f4CorootCoordinates M (Additive.ofMul χ)) := by
  apply TorusCharacter.pointCharacter_injective
  ext x
  change χ.pointCharacter ((f4CorootProduct M).onPoints x) = _
  rw [f4CorootProduct_apply, map_list_prod, List.map_ofFn, List.prod_ofFn]
  rw [TorusCharacter.pointCharacter_dLaurentCharacter]
  change (∏ i : Fin 4, χ.pointCharacter
    ((M.rootData.rootCocharacter (f4SimpleRoot M i)).onPoints
      ((dCoordinateCharacter 4 i).onPoints x))) =
    ((∏ i, dPointEquiv 4 x i ^ f4CorootCoordinates M (Additive.ofMul χ) i : kˣ) : k)
  rw [Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [M.realization.weightPairing_spec χ (f4SimpleRoot M i)]
  rw [dCoordinateCharacter_apply, f4CorootCoordinates_apply]
  exact (Units.val_zpow_eq_zpow_val _ _).symm

/-- Every character of the rank-four diagonal torus is pulled back from the actual torus. -/
theorem f4CorootProduct_pullback_surjective
    (M : RootSystemModel typeF4RootPairingULift G) :
    Function.Surjective (TorusCharacter.pullback (f4CorootProduct M)) := by
  intro χ
  obtain ⟨z, rfl⟩ := dLaurentCharacter_surjective 4 χ
  obtain ⟨ψ, hψ⟩ := f4CorootCoordinates_surjective M z
  refine ⟨ψ.toMul, ?_⟩
  rw [f4CorootProduct_pullback]
  exact congrArg (dLaurentCharacter 4) hψ

/-- The F4 coroot product is injective even before proving that it covers the torus. -/
theorem f4CorootProduct_injective
    (M : RootSystemModel typeF4RootPairingULift G) :
    Function.Injective M.f4CorootProduct.onPoints :=
  M.f4CorootProduct.toVariety.injective_of_pullbackRingHom_surjective
    (torusMorphism_pullbackRingHom_surjective_of_character_pullback_surjective
      (dVariety_isTorus 4) M.maximalTorus.1 M.f4CorootProduct
      M.f4CorootProduct_pullback_surjective)

/-- Character separation excludes a proper image for the coroot product. -/
theorem f4CorootProduct_surjective_of_coordinates_injective
    (M : RootSystemModel typeF4RootPairingULift G)
    (hinj : Function.Injective (f4CorootCoordinates M)) :
    Function.Surjective (f4CorootProduct M).onPoints := by
  by_contra h
  obtain ⟨χ, hχ, y, hy⟩ := IsTorus.exists_character_ne_one_of_not_surjective
    (dVariety_isTorus 4) M.maximalTorus.1 (f4CorootProduct M) h
  have hpull : TorusCharacter.pullback (f4CorootProduct M) χ = 1 := by
    apply Morphism.ext
    funext x
    exact hχ x
  have hzero : f4CorootCoordinates M (Additive.ofMul χ) = 0 := by
    apply dLaurentCharacter_injective (k := k) 4
    rw [← f4CorootProduct_pullback, hpull]
    exact (map_zero (dLaurentCharacterHom (k := k) 4)).symm
  have htrivial : χ = 1 := by
    have hz : Additive.ofMul χ = 0 := hinj (hzero.trans (map_zero _).symm)
    exact congrArg Additive.toMul hz
  exact hy (congrArg (fun f : TorusWeight M.torus => f.onPoints y) htrivial)

/-- The actual coroot product is an algebraic isomorphism when coroots separate characters. -/
theorem f4CorootProduct_iso_of_coordinates_injective
    (M : RootSystemModel typeF4RootPairingULift G)
    (hinj : Function.Injective (f4CorootCoordinates M)) :
    ∃ e : Theory.AlgebraicGroup.Iso (dVariety k 4) M.torus.carrierVariety,
      e.hom = f4CorootProduct M :=
  torusIso_of_surjective_of_character_pullback_surjective
    (dVariety_isTorus 4) M.maximalTorus.1 (f4CorootProduct M)
    (f4CorootProduct_surjective_of_coordinates_injective M hinj)
    (f4CorootProduct_pullback_surjective M)


end Theory.AlgebraicGroup.RootSystemModel
