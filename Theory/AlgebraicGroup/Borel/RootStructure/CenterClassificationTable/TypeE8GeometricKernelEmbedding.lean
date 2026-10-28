module

public import Theory.AlgebraicGroup.Borel.RootStructure.CenterClassificationTable.TypeE8Core
public import Theory.AlgebraicGroup.RootSubgroups.Center
public import Theory.AlgebraicGroup.Tori.Character.Duality

/-!
The geometric reduction for the type `E8` row of GLS3, Theorem 1.12.5(c)-(d)
and Table 1.12.5.

Fix a maximal torus and number its simple roots. A basis of the integral torus
character lattice gives eight multiplicative coordinates on torus points. If
each simple root is the corresponding column of the standard `E8` Cartan
matrix in this basis, a central point satisfies the eight Cartan relations:
centrality and the realized root-subgroup conjugation equation make every
simple root evaluate to one. Canonical character duality then proves that the
coordinate homomorphism is injective.

`E8TorusCharacterCoordinates` is the exact integral root-datum bridge used by
this argument. The current `HasRootSystemType` contract only identifies the
pairing between realized roots; it does not supply this character-lattice basis
or its simple-root coordinate formula. Likewise, the public construction takes
the self-centralizer equality whose reductive maximal-torus proof belongs to
the lower centralizer layer. No placeholder-backed numbered theorem is used.
-/

namespace Theory.AlgebraicGroup

open scoped BigOperators

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Integral character coordinates compatible with the standard `E8` Cartan
matrix. This is the character-lattice component missing from the current
`HasRootSystemType` witness. -/
public structure E8TorusCharacterCoordinates
    {K : Variety k} [AlgebraicGroup K]
    (T : ClosedSubgroup K) (D : RootGroupData K T) where
  simpleRoot : Fin 8 ≃ {alpha : D.Root // alpha ∈ D.simple}
  characterBasis : Module.Basis (Fin 8) ℤ (Additive (TorusWeight T))
  rootWeight_eq_cartanColumn : ∀ j,
    D.rootWeight (simpleRoot j).1 =
      ∏ i, Additive.toMul (characterBasis i) ^
        dynkinCartanEntry ⟨.E8, 8⟩ i j

private def centerToTorusPointHom
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup) :
    Subgroup.center (Variety.Point K) →* Variety.Point T.carrierVariety := by
  let centerToTorusSubgroup :
      Subgroup.center (Variety.Point K) →* T.toSubgroup :=
    (Subgroup.center (Variety.Point K)).subtype.codRestrict T.toSubgroup
      (fun z => hcenter z.property)
  exact (Equiv.mulEquiv T.pointEquiv).symm.toMonoidHom.comp centerToTorusSubgroup

private noncomputable def torusBasisCoordinateHom
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (b : Module.Basis (Fin 8) ℤ (Additive (TorusWeight T))) :
    Variety.Point T.carrierVariety →* (Fin 8 → kˣ) where
  toFun := fun t i => torusPointEval T.carrierVariety t (Additive.toMul (b i))
  map_one' := by
    funext i
    exact DFunLike.congr_fun (torusPointEval T.carrierVariety).map_one
      (Additive.toMul (b i))
  map_mul' := by
    intro x y
    funext i
    exact DFunLike.congr_fun ((torusPointEval T.carrierVariety).map_mul x y)
      (Additive.toMul (b i))

private noncomputable def e8CenterCoordinateHom
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (C : E8TorusCharacterCoordinates T D)
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup) :
    Subgroup.center (Variety.Point K) →* (Fin 8 → kˣ) :=
  (torusBasisCoordinateHom T C.characterBasis).comp
    (centerToTorusPointHom T hcenter)

omit [IsAlgClosed k] in
private lemma centerToTorusPointHom_includePoint
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup)
    (z : Subgroup.center (Variety.Point K)) :
    T.includePoint (centerToTorusPointHom T hcenter z) = z.1 := by
  change (T.pointEquiv
    (T.pointEquiv.symm ⟨z.1, hcenter z.property⟩)).val = z.1
  rw [T.pointEquiv.apply_symm_apply]

omit [IsAlgClosed k] in
private lemma rootWeight_pointCharacter_eq_one_of_mem_center
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (z : Subgroup.center (Variety.Point K))
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup)
    (alpha : D.Root) :
    (D.rootWeight alpha).pointCharacter (centerToTorusPointHom T hcenter z) = 1 := by
  let s : Variety.Point T.carrierVariety := centerToTorusPointHom T hcenter z
  let x : OneParameterParametrization (D.rootSubgroup alpha).carrierVariety :=
    Classical.choice (hD.2.2.1 alpha).1.2
  have hcomm :
      (D.rootSubgroup alpha).includePoint (x.value 1) * z.1 =
        z.1 * (D.rootSubgroup alpha).includePoint (x.value 1) :=
    Subgroup.mem_center_iff.mp z.property _
  have hconj :
      z.1⁻¹ * (D.rootSubgroup alpha).includePoint (x.value 1) * z.1 =
        (D.rootSubgroup alpha).includePoint (x.value 1) := by
    calc
      _ = z.1⁻¹ * ((D.rootSubgroup alpha).includePoint (x.value 1) * z.1) := by
        rw [mul_assoc]
      _ = z.1⁻¹ * (z.1 * (D.rootSubgroup alpha).includePoint (x.value 1)) := by
        rw [hcomm]
      _ = _ := by simp
  have hweight := (hD.2.2.1 alpha).2 x 1 s
  rw [centerToTorusPointHom_includePoint T hcenter z, hconj, mul_one] at hweight
  have hxval : x.value 1 = x.value ((D.rootWeight alpha).pointCharacter s) := by
    apply (D.rootSubgroup alpha).inclusion_injective
    exact hweight
  have hkplus :
      kPlusPoint 1 = kPlusPoint ((D.rootWeight alpha).pointCharacter s) := by
    have h := congrArg x.inv.onPoints hxval
    simpa only [OneParameterParametrization.value, x.hom_inv_id] using h
  exact (congrArg (fun q : Variety.Point (KPlus k) => q.val PUnit.unit) hkplus).symm

private noncomputable def e8CenterToCartanRelationKernelOfContainment
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E8TorusCharacterCoordinates T D)
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup) :
    Subgroup.center (Variety.Point K) →*
      e8CartanRelationKernel (k := k) :=
  (e8CenterCoordinateHom T D C hcenter).codRestrict
    (e8CartanRelationKernel (k := k)) (by
      intro z j
      change ∏ i,
          torusPointEval T.carrierVariety (centerToTorusPointHom T hcenter z)
            (Additive.toMul (C.characterBasis i)) ^
              dynkinCartanEntry ⟨.E8, 8⟩ i j = 1
      calc
        _ = torusPointEval T.carrierVariety
              (centerToTorusPointHom T hcenter z)
              (∏ i, Additive.toMul (C.characterBasis i) ^
                dynkinCartanEntry ⟨.E8, 8⟩ i j) := by
            rw [map_prod]
            simp only [map_zpow]
        _ = torusPointEval T.carrierVariety
              (centerToTorusPointHom T hcenter z)
              (D.rootWeight (C.simpleRoot j).1) := by
            rw [C.rootWeight_eq_cartanColumn]
        _ = 1 := by
            apply Units.ext
            exact rootWeight_pointCharacter_eq_one_of_mem_center
              T D hD z hcenter (C.simpleRoot j).1)

private lemma torusPoint_eq_of_basis_coordinates_eq
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (b : Module.Basis (Fin 8) ℤ (Additive (TorusCharacter T)))
    {x y : Variety.Point T}
    (h : ∀ i,
      torusPointEval T x (Additive.toMul (b i)) =
        torusPointEval T y (Additive.toMul (b i))) :
    x = y := by
  apply (torusPointEval_bijective hT).injective
  apply MonoidHom.ext
  intro chi
  have hchi : chi = ∏ i,
      (Additive.toMul (b i)) ^ (b.repr (Additive.ofMul chi)) i := by
    apply Additive.ofMul.injective
    simp
  rw [hchi, map_prod, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow, map_zpow, h i]

private theorem e8CenterToCartanRelationKernelOfContainment_injective
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hT : IsSubtorus T) (hD : D.IsRealization)
    (C : E8TorusCharacterCoordinates T D)
    (hcenter : Subgroup.center (Variety.Point K) ≤ T.toSubgroup) :
    Function.Injective
      (e8CenterToCartanRelationKernelOfContainment T D hD C hcenter) := by
  intro x y hxy
  have hcoordinates : ∀ i,
      torusPointEval T.carrierVariety (centerToTorusPointHom T hcenter x)
          (Additive.toMul (C.characterBasis i)) =
        torusPointEval T.carrierVariety (centerToTorusPointHom T hcenter y)
          (Additive.toMul (C.characterBasis i)) := by
    intro i
    have hi := congrFun (congrArg Subtype.val hxy) i
    change (e8CenterCoordinateHom T D C hcenter x) i =
      (e8CenterCoordinateHom T D C hcenter y) i at hi
    exact hi
  have htorus : centerToTorusPointHom T hcenter x =
      centerToTorusPointHom T hcenter y :=
    torusPoint_eq_of_basis_coordinates_eq hT C.characterBasis hcoordinates
  apply Subtype.ext
  calc
    x.1 = T.includePoint (centerToTorusPointHom T hcenter x) :=
      (centerToTorusPointHom_includePoint T hcenter x).symm
    _ = T.includePoint (centerToTorusPointHom T hcenter y) := congrArg _ htorus
    _ = y.1 := centerToTorusPointHom_includePoint T hcenter y

/-- Evaluation of the eight fundamental character coordinates sends every
central point into the common `E8` Cartan-relation kernel. -/
public noncomputable def e8CenterToCartanRelationKernel
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hD : D.IsRealization)
    (C : E8TorusCharacterCoordinates T D)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup) :
    Subgroup.center (Variety.Point K) →*
      e8CartanRelationKernel (k := k) :=
  e8CenterToCartanRelationKernelOfContainment T D hD C
    (center_le_torus_of_centralizer_eq T hcentralizer)

/-- The `E8` center-coordinate map is faithful because a basis of torus
characters determines every torus point. -/
public theorem e8CenterToCartanRelationKernel_injective
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (D : RootGroupData K T) (hT : IsSubtorus T) (hD : D.IsRealization)
    (C : E8TorusCharacterCoordinates T D)
    (hcentralizer : T.centralizer.toSubgroup = T.toSubgroup) :
    Function.Injective
      (e8CenterToCartanRelationKernel T D hD C hcentralizer) := by
  exact e8CenterToCartanRelationKernelOfContainment_injective T D hT hD C
    (center_le_torus_of_centralizer_eq T hcentralizer)

end Theory.AlgebraicGroup
