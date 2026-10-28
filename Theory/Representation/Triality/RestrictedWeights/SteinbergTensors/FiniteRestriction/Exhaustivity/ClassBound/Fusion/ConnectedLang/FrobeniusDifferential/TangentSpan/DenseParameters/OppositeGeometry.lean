module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Parameters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.DenseParameters.Products
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# The opposite choice of D4 root geometry

Keep the given algebraic group and torus. Label each root subgroup by the
opposite old root, invert its character and coroot, and invert the weight
coordinates. The abstract based root pairing is unchanged. Swapping the
Borel witnesses gives the new big cell; inversion transfers density of their
product. The diagram commutes with root negation, so the original graph and
Frobenius maps satisfy all fields of the new geometry.

Positive root covers for this opposite geometry become negative root covers
for the original geometry by mapping the ordered root list through negation.
This lets the same source theorem supply both signs in Steinberg 6.2(b--c),
`refs/KGroup/GLS3/Chapter2St2.tex`, without a new carrier or a model comparison.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped Pointwise
noncomputable section
universe u
namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

variable {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}

/-- Opposite root labels, with inverse characters and cocharacters. -/
public abbrev RootGroupData.opposite (D : RootGroupData K T) : RootGroupData K T where
  Root := D.Root
  rootWeight a := (D.rootWeight a)⁻¹
  rootSubgroup a := D.rootSubgroup (D.neg a)
  neg := D.neg
  add := D.add
  pairing := D.pairing
  weightPairing χ a := D.weightPairing χ⁻¹ a
  rootCocharacter a := (D.rootCocharacter a).comp
    { toVariety := Theory.AlgebraicGroup.invMorphism _
      map_one := inv_one
      map_mul x y := by
        change (x * y)⁻¹ = x⁻¹ * y⁻¹
        rw [mul_inv_rev]
        exact isMulCommutative_iff.mp (dVariety_isMulCommutative 1) _ _ }
  reflect := D.reflect
  positive := D.positive
  simple := D.simple
  height := D.height

/-- The opposite data still realize the actual torus roots. -/
public theorem RootGroupData.opposite_isRealization [IsAlgClosed k] (D : RootGroupData K T)
    (hD : D.IsRealization) : (RootGroupData.opposite D).IsRealization := by
  rcases hD with ⟨hinj, hrange, hroot, hneg, hadd, hreflect, hdiag, hpair,
    hheightneg, hheightadd, hpos, hsimple, hcochar⟩
  refine ⟨fun a b h => hinj (inv_injective h), ?_, ?_, ?_, ?_, ?_,
    hdiag, ?_, hheightneg, hheightadd, hpos, hsimple, ?_⟩
  · change Set.range (fun a => (D.rootWeight a)⁻¹) = _
    rw [← hrange]
    ext χ
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨D.neg a, hneg a⟩
    · rintro ⟨a, rfl⟩
      exact ⟨D.neg a, by simp only [hneg, inv_inv]⟩
  · intro a
    change IsTorusRootSubgroup T (D.rootSubgroup (D.neg a)) ∧
      RootWeightEquation T (D.rootSubgroup (D.neg a)) (D.rootWeight a)⁻¹
    rw [← hneg]
    exact hroot (D.neg a)
  · intro a
    change (D.rootWeight (D.neg a))⁻¹ = ((D.rootWeight a)⁻¹)⁻¹
    rw [hneg]
  · intro a b c h
    change (D.rootWeight c)⁻¹ = (D.rootWeight a)⁻¹ * (D.rootWeight b)⁻¹
    rw [hadd a b c h, mul_inv]
  · intro a b
    change (D.rootWeight (D.reflect a b))⁻¹ =
      (D.rootWeight b)⁻¹ * ((D.rootWeight a)⁻¹) ^ (-D.pairing b a)
    rw [hreflect, mul_inv, inv_zpow]
  · intro a b
    change D.weightPairing ((D.rootWeight a)⁻¹)⁻¹ b = D.pairing a b
    rw [inv_inv, hpair]
  · intro χ a t
    have h := hcochar χ⁻¹ a t
    change χ.pointCharacter ((D.rootCocharacter a).onPoints t⁻¹) = _
    rw [(D.rootCocharacter a).map_inv]
    change (dPointEquiv 1 (χ.onPoints (((D.rootCocharacter a).onPoints t)⁻¹)) 0 : k) = _
    rw [χ.map_inv]
    exact h

/-- Opposite labels preserve completeness of root addition. -/
public theorem RootGroupData.opposite_isRootAdditionComplete [IsAlgClosed k] (D : RootGroupData K T)
    (hD : D.IsRootAdditionComplete) : (RootGroupData.opposite D).IsRootAdditionComplete := by
  intro a b c h
  apply hD
  apply inv_injective
  simpa only [mul_inv] using h

/-- Generation in the new labels is generation in the old negated root set. -/
public theorem RootGroupData.opposite_generated [IsAlgClosed k] (D : RootGroupData K T)
    (hD : D.IsRealization) (A : Set D.Root) :
    RootSubgroupGenerated (RootGroupData.opposite D) A =
      RootSubgroupGenerated D (D.neg ⁻¹' A) := by
  apply le_antisymm
  · rw [RootSubgroupGenerated_le_iff]
    intro a ha
    exact rootSubgroup_le_RootSubgroupGenerated D
      (by change D.neg (D.neg a) ∈ A; rwa [hD.neg_neg])
  · rw [RootSubgroupGenerated_le_iff]
    intro a ha
    have h := rootSubgroup_le_RootSubgroupGenerated (RootGroupData.opposite D)
      (A := A) (α := D.neg a) ha
    change (D.rootSubgroup (D.neg (D.neg a))).toSubgroup ≤ _ at h
    simpa only [hD.neg_neg] using h

private theorem reverse_dense {D : RootGroupData K T} {P : Set D.Root}
    (H : OppositeBorelBigCell T D P) :
    Dense ((H.data.Bopp.toSubgroup : Set (Variety.Point K)) *
      (H.data.B.toSubgroup : Set (Variety.Point K))) := by
  let e : Variety.Point K ≃ₜ Variety.Point K :=
    { toFun := fun g => g⁻¹
      invFun := fun g => g⁻¹
      left_inv := inv_inv
      right_inv := inv_inv
      continuous_toFun := (Theory.AlgebraicGroup.invMorphism K).continuous
      continuous_invFun := (Theory.AlgebraicGroup.invMorphism K).continuous }
  apply (H.product_dense.preimage e.isOpenMap).mono
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx
  change a * b = x⁻¹ at hab
  refine Set.mem_mul.mpr ⟨b⁻¹, H.data.Bopp.toSubgroup.inv_mem hb,
    a⁻¹, H.data.B.toSubgroup.inv_mem ha, ?_⟩
  rw [← mul_inv_rev, hab, inv_inv]

/-- Swap both Borel witnesses and transport their dense product by inversion. -/
public def OppositeBorelBigCell.oppositeRootData [IsAlgClosed k] {D : RootGroupData K T}
    (hD : D.IsRealization) (H : OppositeBorelBigCell T D D.positive) :
    OppositeBorelBigCell T (RootGroupData.opposite D) (RootGroupData.opposite D).positive := by
  have hpos : RootSubgroupGenerated (RootGroupData.opposite D) D.positive =
      RootSubgroupGenerated D (D.neg ⁻¹' D.positive) := RootGroupData.opposite_generated D hD _
  have hneg : RootSubgroupGenerated (RootGroupData.opposite D) (D.neg ⁻¹' D.positive) =
      RootSubgroupGenerated D D.positive := by
    rw [RootGroupData.opposite_generated]
    congr 1
    ext a
    change D.neg (D.neg a) ∈ D.positive ↔ a ∈ D.positive
    rw [hD.neg_neg]
    exact hD
  exact
    { data :=
        { positive := H.data.positive
          B := H.data.Bopp
          Bopp := H.data.B
          B_isBorel := H.data.Bopp_isBorel
          Bopp_isBorel := H.data.B_isBorel
          positive_witness :=
            { unipotent := H.data.opposite_witness.unipotent
              root_generated := H.data.opposite_witness.root_generated.trans hpos.symm
              borel := H.data.Bopp_isBorel
              radical := H.data.opposite_witness.radical
              torus_unipotent_generate := H.data.opposite_witness.torus_unipotent_generate }
          opposite_witness :=
            { unipotent := H.data.positive_witness.unipotent
              root_generated := H.data.positive_witness.root_generated.trans hneg.symm
              borel := H.data.B_isBorel
              radical := H.data.positive_witness.radical
              torus_unipotent_generate := H.data.positive_witness.torus_unipotent_generate } }
      intersection_eq_torus := (inf_comm _ _).trans H.intersection_eq_torus
      product_dense := reverse_dense H }

end Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
private theorem Geometry.neg_diagram (S : Geometry K) (a : S.roots.Root) :
    S.roots.neg (S.rootIndex.symm (typeD4DiagramEquiv.indexEquiv (S.rootIndex a))) =
      S.rootIndex.symm (typeD4DiagramEquiv.indexEquiv (S.rootIndex (S.roots.neg a))) := by
  apply S.rootIndex.injective
  simp only [S.based.2.2.1, Equiv.apply_symm_apply]
  apply (typeDRootPairing 2).root.injective
  rw [(typeDRootPairing 2).root_reflectionPerm,
    (typeDRootPairing 2).reflection_apply_self]
  have hmap := typeD4DiagramEquiv.toHom.root_weightMap_apply
  calc
    -(typeDRootPairing 2).root (typeD4DiagramEquiv.indexEquiv (S.rootIndex a)) =
        -(typeD4DiagramEquiv.weightMap ((typeDRootPairing 2).root (S.rootIndex a))) := by
          rw [hmap]
    _ = typeD4DiagramEquiv.weightMap (-((typeDRootPairing 2).root (S.rootIndex a))) :=
      (map_neg _ _).symm
    _ = typeD4DiagramEquiv.weightMap ((typeDRootPairing 2).root
        ((typeDRootPairing 2).reflectionPerm (S.rootIndex a) (S.rootIndex a))) := by
      rw [(typeDRootPairing 2).root_reflectionPerm,
        (typeDRootPairing 2).reflection_apply_self]
    _ = _ := hmap _

/-- The opposite root geometry on the same ambient algebraic group and torus. -/
public abbrev Geometry.opposite (S : Geometry K) : Geometry K where
  simple := S.simple
  universal := S.universal
  torus := S.torus
  maximalTorus := S.maximalTorus
  roots := RootGroupData.opposite S.roots
  realized := RootGroupData.opposite_isRealization S.roots S.realized
  additionComplete := RootGroupData.opposite_isRootAdditionComplete S.roots S.additionComplete
  rootIndex := S.rootIndex
  based := S.based
  positive := S.positive
  simpleRoot := S.simpleRoot
  simpleRoot_index := S.simpleRoot_index
  bigCell := OppositeBorelBigCell.oppositeRootData S.realized S.bigCell
  weight := S.weight.trans (MulEquiv.inv (TorusWeight S.torus))
  weight_coordinate a i := by
    change S.roots.weightPairing ((S.weight (Multiplicative.ofAdd a))⁻¹)⁻¹
      (S.simpleRoot i).val = a i
    rw [inv_inv, S.weight_coordinate]
  rootParameter a := S.rootParameter (S.roots.neg a)
  diagram := S.diagram
  diagram_three := S.diagram_three
  diagram_root a t := by
    change S.diagram.toMulEquiv
      ((S.roots.rootSubgroup (S.roots.neg a)).includePoint
        ((S.rootParameter (S.roots.neg a)).value t)) =
      (S.roots.rootSubgroup (S.roots.neg
        (S.rootIndex.symm (typeD4DiagramEquiv.indexEquiv (S.rootIndex a))))).includePoint
        ((S.rootParameter (S.roots.neg
          (S.rootIndex.symm (typeD4DiagramEquiv.indexEquiv (S.rootIndex a))))).value t)
    rw [S.neg_diagram]
    exact S.diagram_root (S.roots.neg a) t
  frobenius := S.frobenius
  frobenius_bijective := S.frobenius_bijective
  frobenius_root a t := S.frobenius_root (S.roots.neg a) t
  commute := S.commute
  fixed_finite := S.fixed_finite

/-- The new positive radical is the original negative radical. -/
public theorem Geometry.opposite_positive_generated (S : Geometry K) :
    RootSubgroupGenerated S.opposite.roots S.opposite.roots.positive =
      RootSubgroupGenerated S.roots (S.roots.neg ⁻¹' S.roots.positive) :=
  RootGroupData.opposite_generated S.roots S.realized _

/-- Transfer a positive cover in opposite labels to the original negative roots. -/
public def Geometry.negativeRootProductCover (S : Geometry K)
    (C : RootProductCover S.opposite.roots S.opposite.rootParameter
      S.opposite.roots.positive) :
    RootProductCover S.roots S.rootParameter (S.roots.neg ⁻¹' S.roots.positive) where
  roots := C.roots.map S.roots.neg
  nodup := C.nodup.map (Function.Involutive.injective S.realized.neg_neg)
  mem_roots a := by
    constructor
    · rintro h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      change S.roots.neg (S.roots.neg b) ∈ S.roots.positive
      rw [S.realized.neg_neg]
      exact (C.mem_roots b).mp hb
    · intro ha
      exact List.mem_map.mpr ⟨S.roots.neg a,
        (C.mem_roots _).mpr ha, S.realized.neg_neg a⟩
  covers x hx := by
    rw [← S.opposite_positive_generated] at hx
    obtain ⟨c, hc⟩ := C.covers x hx
    have hlen : (C.roots.map S.roots.neg).length = C.roots.length := List.length_map _
    refine ⟨fun i => c (Fin.cast hlen i), ?_⟩
    rw [← hc]
    unfold toralOrderedRootProduct
    congr 1
    rw [List.ofFn_congr hlen]
    apply List.ofFn_inj.mpr
    funext i
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.cast_cast, Fin.cast_refl]
    have hget : (C.roots.map S.roots.neg)[i.val] = S.roots.neg C.roots[i.val] :=
      List.getElem_map (l := C.roots) (f := S.roots.neg)
    exact congrArg (fun a => (S.roots.rootSubgroup a).includePoint
      ((S.rootParameter a).value (c i))) hget

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
