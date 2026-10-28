module

public import Theory.AlgebraicGroup.Bor1.ProductTangent
public import Theory.AlgebraicGroup.ClosedSubgroup.TangentIntersectionFoundation
public import Theory.AlgebraicGroup.Morphism.ClosedImage

/-!
# Characteristic-zero tangents of closed-subgroup preimages

For an algebraic-group morphism `f : G -> H` and a closed subgroup `P` of `H`,
this module identifies the identity tangent range of the reduced closed
preimage with the inverse image under `d f` of the tangent range of `P`.

The proof intersects the closed graph of `f` in `G x H` with the reduced
preimage of `P` under second projection.  The product-tangent decomposition
constructs the required tangent in the projection preimage, and exact
characteristic-zero tangent control for closed-subgroup intersections lifts it
to the graph intersection.  First projection then returns a tangent of the
original preimage.  The argument uses Cartier/Hopf reducedness through
`identityTangent_range_eq_inf_charZero`; it does not infer membership in a
radical ideal merely from derivatives of defining equations.

This is the general preimage form of the automatic characteristic-zero
separability principle in Bor1 Chapter 3, 9.1.
-/

universe u

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option linter.style.haveILetI false

private theorem identityTangent_graph_mem_range
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H)
    (A : ClosedSubgroup (Variety.prod G H))
    (hA : A = (AlgebraicGroup.Morphism.prod
      (AlgebraicGroup.Morphism.id G) f).imageClosedSubgroup)
    (D : IdentityPointDerivation G) :
    letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
    identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.prod
        (AlgebraicGroup.Morphism.id G) f) D ∈
      LinearMap.range (identityTangentMorphismLinearMap A.inclusion) := by
  let graph := AlgebraicGroup.Morphism.prod
    (AlgebraicGroup.Morphism.id G) f
  letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  let hmap : ∀ x, graph.onPoints x ∈ A.toSubgroup := by
    intro x
    rw [hA]
    exact ⟨x, rfl⟩
  let r : AlgebraicGroup.Morphism G A.carrierVariety :=
    graph.codRestrictClosedSubgroup A hmap
  have hfactor : A.inclusion.comp r = graph := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact graph.codRestrictClosedSubgroup_inclusion_apply A hmap x
  refine ⟨identityTangentMorphismLinearMap r D, ?_⟩
  calc
    identityTangentMorphismLinearMap A.inclusion
        (identityTangentMorphismLinearMap r D) =
        identityTangentMorphismLinearMap (A.inclusion.comp r) D := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap graph D := by rw [hfactor]

private theorem identityTangent_sndPreimage_pair_mem_range
    {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (P : ClosedSubgroup H) (B : ClosedSubgroup (Variety.prod G H))
    (hB : B = (AlgebraicGroup.Morphism.snd G H).closedSubgroupPreimage P)
    (D : IdentityPointDerivation G)
    (E : IdentityPointDerivation P.carrierVariety) :
    letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
    identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H) D +
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
          (identityTangentMorphismLinearMap P.inclusion E) ∈
      LinearMap.range (identityTangentMorphismLinearMap B.inclusion) := by
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
  letI : AlgebraicGroup (Variety.prod G P.carrierVariety) :=
    AlgebraicGroup.prod G P.carrierVariety
  let ambient : AlgebraicGroup.Morphism
      (Variety.prod G P.carrierVariety) (Variety.prod G H) :=
    AlgebraicGroup.Morphism.prod
      (AlgebraicGroup.Morphism.fst G P.carrierVariety)
      (P.inclusion.comp (AlgebraicGroup.Morphism.snd G P.carrierVariety))
  have hmap : ∀ x, ambient.onPoints x ∈ B.toSubgroup := by
    intro x
    rw [hB]
    change (AlgebraicGroup.Morphism.snd G H).onPoints
      (ambient.onPoints x) ∈ P.toSubgroup
    change P.inclusion.onPoints
      ((AlgebraicGroup.Morphism.snd G P.carrierVariety).onPoints x) ∈
        P.toSubgroup
    exact (P.pointEquiv _).property
  let r : AlgebraicGroup.Morphism
      (Variety.prod G P.carrierVariety) B.carrierVariety :=
    ambient.codRestrictClosedSubgroup B hmap
  have hfactor : B.inclusion.comp r = ambient := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    exact ambient.codRestrictClosedSubgroup_inclusion_apply B hmap x
  have hleft : ambient.comp
      (AlgebraicGroup.Morphism.inl G P.carrierVariety) =
      AlgebraicGroup.Morphism.inl G H := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (Variety.prodPointEquiv G H).injective
    rfl
  have hright : ambient.comp
      (AlgebraicGroup.Morphism.inr G P.carrierVariety) =
      (AlgebraicGroup.Morphism.inr G H).comp P.inclusion := by
    apply AlgebraicGroup.Morphism.ext
    funext x
    apply (Variety.prodPointEquiv G H).injective
    rfl
  let W : IdentityPointDerivation (Variety.prod G P.carrierVariety) :=
    identityTangentMorphismLinearMap
        (AlgebraicGroup.Morphism.inl G P.carrierVariety) D +
      identityTangentMorphismLinearMap
        (AlgebraicGroup.Morphism.inr G P.carrierVariety) E
  refine ⟨identityTangentMorphismLinearMap r W, ?_⟩
  calc
    identityTangentMorphismLinearMap B.inclusion
        (identityTangentMorphismLinearMap r W) =
        identityTangentMorphismLinearMap (B.inclusion.comp r) W := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap ambient W := by rw [hfactor]
    _ = identityTangentMorphismLinearMap ambient
          (identityTangentMorphismLinearMap
              (AlgebraicGroup.Morphism.inl G P.carrierVariety) D +
            identityTangentMorphismLinearMap
              (AlgebraicGroup.Morphism.inr G P.carrierVariety) E) := rfl
    _ = identityTangentMorphismLinearMap ambient
            (identityTangentMorphismLinearMap
              (AlgebraicGroup.Morphism.inl G P.carrierVariety) D) +
          identityTangentMorphismLinearMap ambient
            (identityTangentMorphismLinearMap
              (AlgebraicGroup.Morphism.inr G P.carrierVariety) E) := by
      rw [map_add]
    _ = identityTangentMorphismLinearMap
            (ambient.comp (AlgebraicGroup.Morphism.inl G P.carrierVariety)) D +
          identityTangentMorphismLinearMap
            (ambient.comp (AlgebraicGroup.Morphism.inr G P.carrierVariety)) E := by
      rw [identityTangentMorphismLinearMap_comp,
        identityTangentMorphismLinearMap_comp]
      rfl
    _ = identityTangentMorphismLinearMap
            (AlgebraicGroup.Morphism.inl G H) D +
          identityTangentMorphismLinearMap
            ((AlgebraicGroup.Morphism.inr G H).comp P.inclusion) E := by
      rw [hleft, hright]
    _ = identityTangentMorphismLinearMap
            (AlgebraicGroup.Morphism.inl G H) D +
          identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
            (identityTangentMorphismLinearMap P.inclusion E) := by
      rw [identityTangentMorphismLinearMap_comp]
      rfl

/-- Over an algebraically closed characteristic-zero field, taking the reduced
closed preimage of a closed subgroup commutes exactly with taking the identity
tangent subspace. -/
public theorem identityTangent_closedSubgroupPreimage_range_eq_comap_charZero
    [CharZero k] {G H : Variety k} [AlgebraicGroup G] [AlgebraicGroup H]
    (f : AlgebraicGroup.Morphism G H) (P : ClosedSubgroup H) :
    LinearMap.range (identityTangentMorphismLinearMap
        (f.closedSubgroupPreimage P).inclusion) =
      Submodule.comap (identityTangentMorphismLinearMap f)
        (LinearMap.range (identityTangentMorphismLinearMap P.inclusion)) := by
  let K := f.closedSubgroupPreimage P
  let graph := AlgebraicGroup.Morphism.prod
    (AlgebraicGroup.Morphism.id G) f
  let A := graph.imageClosedSubgroup
  let B := (AlgebraicGroup.Morphism.snd G H).closedSubgroupPreimage P
  let I := A.inter B
  letI : AlgebraicGroup K.carrierVariety := K.carrierAlgebraicGroup
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  letI : AlgebraicGroup A.carrierVariety := A.carrierAlgebraicGroup
  letI : AlgebraicGroup B.carrierVariety := B.carrierAlgebraicGroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  apply le_antisymm
  · rintro _ ⟨X, rfl⟩
    rw [Submodule.mem_comap]
    refine ⟨identityTangentMorphismLinearMap (f.preimageRestriction P) X, ?_⟩
    have hfactor : P.inclusion.comp (f.preimageRestriction P) =
        f.comp K.inclusion := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      exact f.preimageRestriction_inclusion_apply P x
    calc
      identityTangentMorphismLinearMap P.inclusion
          (identityTangentMorphismLinearMap (f.preimageRestriction P) X) =
          identityTangentMorphismLinearMap
            (P.inclusion.comp (f.preimageRestriction P)) X := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap (f.comp K.inclusion) X := by
        rw [hfactor]
      _ = identityTangentMorphismLinearMap f
          (identityTangentMorphismLinearMap K.inclusion X) := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
  · intro D hD
    rw [Submodule.mem_comap] at hD
    rcases hD with ⟨E, hE⟩
    let Z : IdentityPointDerivation (Variety.prod G H) :=
      identityTangentMorphismLinearMap graph D
    have hZA : Z ∈ LinearMap.range
        (identityTangentMorphismLinearMap A.inclusion) := by
      exact identityTangent_graph_mem_range f A rfl D
    have hgraph : Z =
        identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inl G H) D +
          identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
            (identityTangentMorphismLinearMap f D) := by
      simpa [Z, graph] using
        (identityTangentMorphismLinearMap_prod_apply
          (AlgebraicGroup.Morphism.id G) f D)
    have hZB : Z ∈ LinearMap.range
        (identityTangentMorphismLinearMap B.inclusion) := by
      have hpair := identityTangent_sndPreimage_pair_mem_range P B rfl D E
      change identityTangentMorphismLinearMap
            (AlgebraicGroup.Morphism.inl G H) D +
          identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.inr G H)
            (identityTangentMorphismLinearMap P.inclusion E) ∈
        LinearMap.range (identityTangentMorphismLinearMap B.inclusion) at hpair
      rw [hE, ← hgraph] at hpair
      exact hpair
    have hZI : Z ∈ LinearMap.range
        (identityTangentMorphismLinearMap I.inclusion) := by
      rw [identityTangent_range_eq_inf_charZero A B]
      exact Submodule.mem_inf.mpr ⟨hZA, hZB⟩
    let q : AlgebraicGroup.Morphism I.carrierVariety G :=
      (AlgebraicGroup.Morphism.fst G H).comp I.inclusion
    have hqmap : ∀ x, q.onPoints x ∈ K.toSubgroup := by
      intro x
      change f.onPoints (q.onPoints x) ∈ P.toSubgroup
      let z := I.inclusion.onPoints x
      have hzI : z ∈ I.toSubgroup := (I.pointEquiv x).property
      have hzAB := (ClosedSubgroup.mem_inter_iff A B z).mp hzI
      have hzA : z ∈ graph.image := hzAB.1
      have hzB : (AlgebraicGroup.Morphism.snd G H).onPoints z ∈
          P.toSubgroup := hzAB.2
      rcases hzA with ⟨a, ha⟩
      have hpair : (a, f.onPoints a) =
          Variety.prodPointEquiv G H z := by
        change Variety.prodPointEquiv G H (graph.onPoints a) =
          Variety.prodPointEquiv G H z
        exact congrArg (Variety.prodPointEquiv G H) ha
      have hq : q.onPoints x = a := by
        change (Variety.prodPointEquiv G H z).1 = a
        exact (congrArg Prod.fst hpair).symm
      rw [hq]
      have hsnd : (Variety.prodPointEquiv G H z).2 = f.onPoints a :=
        (congrArg Prod.snd hpair).symm
      change (Variety.prodPointEquiv G H z).2 ∈ P.toSubgroup at hzB
      rwa [hsnd] at hzB
    let p : AlgebraicGroup.Morphism I.carrierVariety K.carrierVariety :=
      q.codRestrictClosedSubgroup K hqmap
    have hpfactor : K.inclusion.comp p = q := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      exact q.codRestrictClosedSubgroup_inclusion_apply K hqmap x
    rcases hZI with ⟨X, hX⟩
    refine ⟨identityTangentMorphismLinearMap p X, ?_⟩
    have hfstGraph : (AlgebraicGroup.Morphism.fst G H).comp graph =
        AlgebraicGroup.Morphism.id G := by
      apply AlgebraicGroup.Morphism.ext
      funext x
      rfl
    calc
      identityTangentMorphismLinearMap K.inclusion
          (identityTangentMorphismLinearMap p X) =
          identityTangentMorphismLinearMap (K.inclusion.comp p) X := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap q X := by rw [hpfactor]
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          (identityTangentMorphismLinearMap I.inclusion X) := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          Z := by rw [hX]
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.fst G H)
          (identityTangentMorphismLinearMap graph D) := rfl
      _ = identityTangentMorphismLinearMap
          ((AlgebraicGroup.Morphism.fst G H).comp graph) D := by
        rw [identityTangentMorphismLinearMap_comp]
        rfl
      _ = identityTangentMorphismLinearMap (AlgebraicGroup.Morphism.id G) D := by
        rw [hfstGraph]
      _ = D := by rw [identityTangentMorphismLinearMap_id]; rfl

end Theory.AlgebraicGroup.Bor1
