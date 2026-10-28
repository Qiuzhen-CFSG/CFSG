module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedLang.FrobeniusDifferential.TangentSpan.Parameters
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.RootProducts

/-!
# Root-product morphisms and surjective coordinates

Multiply the actual torus coordinate and two ordered lists of actual root
parameters. The domain is the prescribed torus times affine space on all roots.
Surjective coordinates for the positive and negative radicals make its range
contain the dense opposite-Borel product. Disjointness of the two root sets
allows their coordinates to occupy the same affine space independently.

The reusable collection lemma needs only successive relative normalization:
a root group normalizing the group of later factors turns their join into
their pointwise product. Induction collects each element, with no uniqueness
or Chevalley-system premise. This is the existence part of Steinberg 6.2(b),
followed by the dominance consequence of 6.2(c), in
`refs/KGroup/GLS3/Chapter2St2.tex`. The induction follows the existence branch
of `ConnectedCentralizer/Bruhat/Coordinates/Product.lean`.

The normalization and coordinate-cover premises remain explicit in this module.
-/

open Theory.AlgebraicGroup
open scoped Pointwise
noncomputable section
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

private def affineCoordinate (ι : Type u) [Finite ι] (i : ι) :
    Variety.Morphism (affineSpaceVariety k ι) (KPlus k) where
  toFun z := kPlusPoint (z.val i)
  regular := by
    intro j
    refine ⟨MvPolynomial.X i, ?_⟩
    intro z
    change z.val i = evalPolynomial z.val (MvPolynomial.X i)
    exact (evalPolynomial_X _ _).symm

private def productMorphism {X : Variety k} :
    List (Variety.Morphism X K) → Variety.Morphism X K
  | [] => Variety.Morphism.const X K 1
  | f :: fs => (Theory.AlgebraicGroup.mulMorphism K).comp (f.pair (productMorphism fs))

omit [CharP k 2] in
private theorem productMorphism_apply {X : Variety k}
    (fs : List (Variety.Morphism X K)) (z : Variety.Point X) :
    (productMorphism fs).toFun z = (fs.map fun f => f.toFun z).prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change f.toFun z * (productMorphism fs).toFun z = _
    rw [ih]
    rfl

namespace Theory.AlgebraicGroup

/-- Surjectivity of ordered root coordinates, without an injectivity requirement. -/
public structure RootProductCover {T : ClosedSubgroup K} (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (P : Set D.Root) where
  roots : List D.Root
  nodup : roots.Nodup
  mem_roots : ∀ a, a ∈ roots ↔ a ∈ P
  covers : ∀ x ∈ RootSubgroupGenerated D P,
    ∃ c, toralOrderedRootProduct D p roots c = x

omit [CharP k 2] in
private theorem rootProduct_covers_of_suffixes {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (rs : List D.Root)
    (hnormal : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ≤
        Subgroup.normalizer (RootSubgroupGenerated D {b | b ∈ bs} : Set (Variety.Point K))) :
    ∀ x ∈ RootSubgroupGenerated D {a | a ∈ rs},
      ∃ c, toralOrderedRootProduct D p rs c = x := by
  let parameter (a : D.Root) : k ≃ (D.rootSubgroup a).toSubgroup :=
    (Multiplicative.ofAdd.trans (additiveGroupPointEquiv k).symm).trans
      ((p a).toMulEquiv.toEquiv.trans (D.rootSubgroup a).pointEquiv)
  have cons (a : D.Root) (rs : List D.Root) (c : Fin (a :: rs).length → k) :
      toralOrderedRootProduct D p (a :: rs) c =
        (parameter a (c 0)).val * toralOrderedRootProduct D p rs (fun i => c i.succ) := by
    rw [toralOrderedRootProduct, List.ofFn_succ, List.prod_cons]
    rfl
  induction rs with
  | nil =>
    intro x hx
    have hx1 : x = 1 := by simpa [RootSubgroupGenerated] using hx
    exact ⟨Fin.elim0, by simpa [toralOrderedRootProduct] using hx1.symm⟩
  | cons a rs ih =>
    have hcover := ih (fun b bs h => hnormal b bs (h.trans (List.suffix_cons a rs)))
    intro x hx
    have hgen : RootSubgroupGenerated D {b | b ∈ a :: rs} =
        (D.rootSubgroup a).toSubgroup ⊔ RootSubgroupGenerated D {b | b ∈ rs} := by
      rw [show {b | b ∈ a :: rs} = {a} ∪ {b | b ∈ rs} by ext; simp,
        RootSubgroupGenerated_union, RootSubgroupGenerated_singleton]
    rw [hgen] at hx
    have hprod := Subgroup.coe_mul_of_left_le_normalizer_right
      (D.rootSubgroup a).toSubgroup (RootSubgroupGenerated D {b | b ∈ rs})
      (hnormal a rs (List.suffix_refl _))
    change x ∈ (↑((D.rootSubgroup a).toSubgroup ⊔
      RootSubgroupGenerated D {b | b ∈ rs}) : Set (Variety.Point K)) at hx
    rw [hprod] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨t, ht⟩ := (parameter a).surjective ⟨y, hy⟩
    obtain ⟨c, hc⟩ := hcover z hz
    refine ⟨Fin.cons t c, ?_⟩
    rw [cons]
    simpa [hc] using congrArg (fun q : (D.rootSubgroup a).toSubgroup =>
      (q : Variety.Point K) * z) ht

/-- Successive relative normalization suffices for existence of root coordinates. -/
public def rootProductCover_of_suffixes {T : ClosedSubgroup K}
    (D : RootGroupData K T)
    (p : ∀ a, OneParameterParametrization (D.rootSubgroup a).carrierVariety)
    (P : Set D.Root) (rs : List D.Root) (hnd : rs.Nodup)
    (hmem : ∀ a, a ∈ rs ↔ a ∈ P)
    (hnormal : ∀ a bs, (a :: bs).IsSuffix rs →
      (D.rootSubgroup a).toSubgroup ≤
        Subgroup.normalizer (RootSubgroupGenerated D {b | b ∈ bs} : Set (Variety.Point K))) :
    RootProductCover D p P where
  roots := rs
  nodup := hnd
  mem_roots := hmem
  covers := by
    have hset : {a | a ∈ rs} = P := Set.ext hmem
    simpa only [hset] using rootProduct_covers_of_suffixes D p rs hnormal

end Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction

private def Geometry.rootListMorphism (S : Geometry K) (rs : List S.roots.Root) :
    Variety.Morphism S.rootProductParameterSpace K := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  exact productMorphism (List.ofFn fun i : Fin rs.length =>
    let a := rs.get i;
    ((S.roots.rootSubgroup a).inclusion.toVariety.comp (S.rootParameter a).hom.toVariety).comp
      ((affineCoordinate S.roots.Root a).comp
        (Variety.Morphism.snd S.torus.carrierVariety (affineSpaceVariety k S.roots.Root))))

private theorem Geometry.rootListMorphism_apply (S : Geometry K) (rs : List S.roots.Root)
    (z : Variety.Point S.rootProductParameterSpace) :
    (S.rootListMorphism rs).toFun z =
      toralOrderedRootProduct S.roots S.rootParameter rs
        (fun i => z.val (Sum.inr (rs.get i))) := by
  rw [Geometry.rootListMorphism, productMorphism_apply, List.map_ofFn]
  rfl

/-- Multiplication of the torus, positive-root list and negative-root list. -/
public def Geometry.rootProductMorphism (S : Geometry K) (positive negative : List S.roots.Root) :
    Variety.Morphism S.rootProductParameterSpace K := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  let t := S.torus.inclusion.toVariety.comp
    (Variety.Morphism.fst S.torus.carrierVariety (affineSpaceVariety k S.roots.Root))
  exact (Theory.AlgebraicGroup.mulMorphism K).comp
    (((Theory.AlgebraicGroup.mulMorphism K).comp (t.pair (S.rootListMorphism positive))).pair
      (S.rootListMorphism negative))

/-- A torus point and all root scalars form a point of the prescribed domain. -/
@[expose] public def Geometry.rootProductParameterPoint (S : Geometry K)
    (t : Variety.Point S.torus.carrierVariety) (c : S.roots.Root → k) :
    Variety.Point S.rootProductParameterSpace := by
  let : Finite S.roots.Root := Finite.of_equiv _ S.rootIndex.symm
  exact (Variety.prodPointEquiv S.torus.carrierVariety
    (affineSpaceVariety k S.roots.Root)).symm (t, affineSpacePoint c)

/-- The constructed morphism evaluates to the intended root product. -/
public theorem Geometry.rootProductMorphism_apply (S : Geometry K)
    (positive negative : List S.roots.Root)
    (t : Variety.Point S.torus.carrierVariety) (c : S.roots.Root → k) :
    (S.rootProductMorphism positive negative).toFun (S.rootProductParameterPoint t c) =
      S.torus.includePoint t *
        toralOrderedRootProduct S.roots S.rootParameter positive (fun i => c (positive.get i)) *
        toralOrderedRootProduct S.roots S.rootParameter negative (fun i => c (negative.get i)) := by
  change S.torus.includePoint t *
    (S.rootListMorphism positive).toFun (S.rootProductParameterPoint t c) *
    (S.rootListMorphism negative).toFun (S.rootProductParameterPoint t c) = _
  rw [S.rootListMorphism_apply, S.rootListMorphism_apply]
  rfl

/-- Surjective coordinates on both radicals give dominance on the actual carrier. -/
public theorem Geometry.exists_dense_root_parameter_morphism_of_covers
    (S : Geometry K)
    (C : RootProductCover S.roots S.rootParameter S.roots.positive)
    (N : RootProductCover S.roots S.rootParameter (S.roots.neg ⁻¹' S.roots.positive)) :
    ∃ f : Variety.Morphism S.rootProductParameterSpace K, Dense (Set.range f.toFun) := by
  classical
  refine ⟨S.rootProductMorphism C.roots N.roots, S.bigCell.product_dense.mono ?_⟩
  intro x hx
  obtain ⟨b, hb, b', hb', rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨t, u, ht, hu, rfl⟩ := (S.bigCell.positive_decomposition b).mp hb
  obtain ⟨t', v, ht', hv, rfl⟩ := (S.bigCell.negative_decomposition b').mp hb'
  have hu' : t'⁻¹ * u * t' ∈ RootSubgroupGenerated S.roots S.roots.positive := by
    have hnorm := torus_le_rootSubgroupGenerated_normalizer S.roots S.realized
      S.roots.positive (S.torus.toSubgroup.inv_mem ht')
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hnorm u).mp hu
  obtain ⟨cp, hcp⟩ := C.covers _ hu'
  obtain ⟨cn, hcn⟩ := N.covers _ hv
  let p := Function.extend C.roots.get cp (fun _ => 0)
  let n := Function.extend N.roots.get cn (fun _ => 0)
  let c : S.roots.Root → k := fun a => if a ∈ S.roots.positive then p a else n a
  have hp : (fun i => c (C.roots.get i)) = cp := by
    funext i
    dsimp only [c]
    rw [if_pos ((C.mem_roots _).mp (List.get_mem C.roots i))]
    exact C.nodup.injective_get.extend_apply cp (fun _ => 0) i
  have hn : (fun i => c (N.roots.get i)) = cn := by
    funext i
    have hneg := (N.mem_roots _).mp (List.get_mem N.roots i)
    have hnot : N.roots.get i ∉ S.roots.positive := by
      intro hpos
      have h : N.roots.get i ∈ (∅ : Set S.roots.Root) :=
        S.bigCell.data.positive.1 ▸ ⟨hpos, hneg⟩
      exact h
    dsimp only [c]
    rw [if_neg hnot]
    exact N.nodup.injective_get.extend_apply cn (fun _ => 0) i
  let tt : Variety.Point S.torus.carrierVariety :=
    S.torus.pointEquiv.symm ⟨t * t', S.torus.toSubgroup.mul_mem ht ht'⟩
  have htt : S.torus.includePoint tt = t * t' :=
    congrArg Subtype.val (S.torus.pointEquiv.apply_symm_apply _)
  refine ⟨S.rootProductParameterPoint tt c, ?_⟩
  rw [S.rootProductMorphism_apply, hp, hn, hcp, hcn, htt]
  group

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
