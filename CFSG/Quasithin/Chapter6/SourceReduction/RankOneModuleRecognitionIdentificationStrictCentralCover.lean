module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictNormalizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictRank
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# The literal central cover in the strict branch

The source identity U intersect V = [V,U]⟨z⟩, together with normal-closure
generation, makes U/⟨z⟩ commutator-generated for K/O₂(K). Since K fixes
Z(U), the literal projection U/⟨z⟩ → U/Z(U) is a central module cover.
Its kernel is bounded by the dual first cohomology of the latter module.
Thus a nontrivial crossed-center image forces nonzero dual cohomology.

This keeps the original layer closure and quotient maps; no equality-branch
CoreData is assumed. Source: Aschbacher--Smith 6.2.15--17, pp.688--690,
and I.1.5, p.408. The exceptional-action consumer is StrictExceptionalCohomology.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open M22Recognition.CentralizerExtension
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

 theorem LocalAnalysis.strict_lift_commutator_generation
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    equalityClosure (T : Subgroup G) L R z =
      ⁅equalityLayerClosure L R z, equalityClosure (T : Subgroup G) L R z⁆ ⊔ equalityLine z := by
  let H := centralizer ({z} : Set G)
  let N := equalityClosure (T : Subgroup G) L R z
  let K := equalityLayerClosure L R z
  let Z := equalityLine z
  let C := ⁅K, N⁆ ⊔ Z
  have hVH : layer L R ≤ H := layer_le_involution_centralizer h611 hz
  have hZ : Z ≤ N := fun x hx => sourceEight_contains _ ((zpowers_le.mpr hz) hx)
  have hline : Z.map H.subtype = zpowers z :=
    map_subgroupOf_eq_of_le ((zpowers_le.mpr hz).trans (inf_le_left.trans hVH))
  have hVK : layer L R ≤ K.map H.subtype := by
    intro v hv
    exact mem_map.mpr ⟨⟨v,hVH hv⟩, le_normalClosure hv, rfl⟩
  have hI : sourceClosure (T : Subgroup G) L R z ⊓ layer L R ≤ C.map H.subtype := by
    rw [A.strict_intersection_eq_commutator_sup_line h611 hnatural hz horder hstrict]
    change _ ≤ (⁅K, N⁆ ⊔ Z).map H.subtype
    rw [Subgroup.map_sup, map_commutator, hline]
    exact sup_le_sup (commutator_mono hVK le_rfl) le_rfl
  apply le_antisymm ?_ (sup_le (commutator_le_right K N) hZ)
  apply normalClosure_le_normal
  intro s hs
  obtain ⟨c, hc, he⟩ := hI (hstrict.le hs)
  exact (Subtype.ext he : c = s) ▸ hc

abbrev StrictLayerActor (L R : Subgroup G) (z : G) :=
  equalityLayerClosure L R z ⧸ pCore 2 (equalityLayerClosure L R z)

 def strictLiftActorMap (L R : Subgroup G) (z : G) :
    StrictLayerActor L R z →* EqualityActor z :=
  QuotientGroup.map _ _ (equalityLayerClosure L R z).subtype
    (by rw [pCore_eq_comap_of_normal])

 def strictLiftProjectionHom (T L R : Subgroup G) (z : G) :
    EqualityVectorQuotient T L R z →* StrictVectorQuotient T L R z := by
  let H := centralizer ({z} : Set G)
  let N := equalityClosure T L R z
  let U := sourceClosure T L R z
  let e : N ≃* U := N.equivMapOfInjective H.subtype H.subtype_injective
  refine QuotientGroup.map _ (center U) e.toMonoidHom ?_
  intro x hx
  apply mem_center_iff.mpr
  intro u
  obtain ⟨v,rfl⟩ := e.surjective u
  change e v * e x = e x * e v
  rw [← map_mul, ← map_mul]
  apply congrArg e
  apply Subtype.ext
  exact mem_center_iff.mp (equalityLine_le_center z hx) v.val

omit [Finite G] in
 theorem strictLiftProjectionHom_mk (T L R : Subgroup G) (z : G)
    (u : equalityClosure T L R z) :
    strictLiftProjectionHom T L R z (QuotientGroup.mk' _ u) =
      QuotientGroup.mk' (center (sourceClosure T L R z))
        ((equalityClosure T L R z).equivMapOfInjective
          (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective u) := rfl

omit [Finite G] in
 theorem strictLiftProjectionHom_surjective (T L R : Subgroup G) (z : G) :
    Function.Surjective (strictLiftProjectionHom T L R z) := by
  intro w
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center (sourceClosure T L R z)) w
  obtain ⟨v,rfl⟩ := ((equalityClosure T L R z).equivMapOfInjective
    (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective).surjective u
  exact ⟨QuotientGroup.mk' _ v,rfl⟩

section Linear
variable [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)]

 def strictLiftRepresentation (A : LocalAnalysis (T : Subgroup G) L M R z) :
    Representation (ZMod 2) (StrictLayerActor L R z)
      (Additive (EqualityVectorQuotient (T : Subgroup G) L R z)) :=
  (equalityRepresentation A).comp (strictLiftActorMap L R z)

omit [Finite G] in
 theorem strictLiftRepresentation_mk (A : LocalAnalysis (T : Subgroup G) L M R z)
    (k : equalityLayerClosure L R z)
    (v : Additive (EqualityVectorQuotient (T : Subgroup G) L R z)) :
    strictLiftRepresentation A (QuotientGroup.mk' _ k) v =
      Additive.ofMul (equalityQuotientAction (T : Subgroup G) L R z k.val v.toMul) := rfl

 theorem LocalAnalysis.strictLift_coinvariants_ker
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Representation.Coinvariants.ker (strictLiftRepresentation A) = ⊤ := by
  let N := equalityClosure (T : Subgroup G) L R z
  let K := equalityLayerClosure L R z
  let Z := equalityLine z
  let q := QuotientGroup.mk' (Z.subgroupOf N)
  let σ := strictLiftRepresentation A
  let D : Subgroup (EqualityVectorQuotient (T : Subgroup G) L R z) :=
    (Representation.Coinvariants.ker σ).toAddSubgroup.toSubgroup'
  let B := (D.comap q).map N.subtype
  have hc : ⁅K,N⁆ ≤ B := by
    apply commutator_le.mpr
    intro k hk u hu
    let c : N := ⟨⁅k,u⁆, commutator_le_right K N (commutator_mem_commutator hk hu)⟩
    refine mem_map.mpr ⟨c, ?_, rfl⟩
    change Additive.ofMul (q c) ∈ Representation.Coinvariants.ker σ
    have he : Additive.ofMul (q c) =
        σ (QuotientGroup.mk' _ ⟨k,hk⟩) (Additive.ofMul (q ⟨u,hu⟩)) -
          Additive.ofMul (q ⟨u,hu⟩) := by
      rw [strictLiftRepresentation_mk]
      change Additive.ofMul (q c) = Additive.ofMul (equalityQuotientAction _ _ _ _ k (q ⟨u,hu⟩)) - Additive.ofMul (q ⟨u,hu⟩)
      rw [equalityQuotientAction_mk]
      change Additive.ofMul (q c) = Additive.ofMul (q _ / q _)
      rw [← map_div]
      apply congrArg Additive.ofMul
      apply congrArg q
      apply Subtype.ext
      change ⁅k,u⁆ = k * u * k⁻¹ / u
      rw [commutatorElement_def,div_eq_mul_inv]
    rw [he]
    exact Representation.Coinvariants.sub_mem_ker _ _
  have hZ : Z ≤ B := by
    intro x hx
    have hxN : x ∈ N := sourceEight_contains _ ((zpowers_le.mpr hz) hx)
    refine mem_map.mpr ⟨⟨x,hxN⟩, ?_, rfl⟩
    change q ⟨x,hxN⟩ ∈ D
    rw [show q ⟨x,hxN⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
    exact D.one_mem
  have hN : N ≤ B := by
    change equalityClosure (T : Subgroup G) L R z ≤ B
    rw [A.strict_lift_commutator_generation h611 hnatural hz horder hstrict]
    exact sup_le hc hZ
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf N) v.toMul
  obtain ⟨u',hu',he⟩ := hN u.property
  have hv : q u ∈ D := (Subtype.ext he : u' = u) ▸ hu'
  change Additive.ofMul (q u) ∈ Representation.Coinvariants.ker σ at hv
  change q u = v.toMul at hu
  rw [hu] at hv
  exact hv

variable [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]

 def strictLayerRepresentation (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Representation (ZMod 2) (StrictLayerActor L R z)
      (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :=
  (strictRepresentation (T : Subgroup G) L R z).comp
    (Subgroup.subtype _ |>.comp
      (A.strict_layerClosure_equiv_image h611 hnatural hz horder hstrict).toMonoidHom)

omit [IsElementaryAbelian 2 (EqualityVectorQuotient (T : Subgroup G) L R z)] in
 theorem strictLayerRepresentation_mk (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (k : equalityLayerClosure L R z)
    (v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)) :
    strictLayerRepresentation A h611 hnatural hz horder hstrict (QuotientGroup.mk' _ k) v =
      Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z k.val v.toMul) := rfl

 def strictLiftProjection (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    (strictLiftRepresentation A).IntertwiningMap
      (strictLayerRepresentation A h611 hnatural hz horder hstrict) :=
  ((strictLiftProjectionHom (T : Subgroup G) L R z).toAdditive.toZModLinearMap 2).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro a v
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective _ a
      obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective _ v.toMul
      have hv : v = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
      rw [hv, strictLiftRepresentation_mk, strictLayerRepresentation_mk]
      change Additive.ofMul (strictLiftProjectionHom (T : Subgroup G) L R z (equalityQuotientAction (T : Subgroup G) L R z k.val (QuotientGroup.mk' _ u))) =
        Additive.ofMul (strictQuotientAction (T : Subgroup G) L R z k.val (strictLiftProjectionHom (T : Subgroup G) L R z (QuotientGroup.mk' _ u)))
      rw [equalityQuotientAction_mk, strictLiftProjectionHom_mk,
        strictLiftProjectionHom_mk]
      apply congrArg Additive.ofMul
      let e : equalityClosure (T : Subgroup G) L R z ≃* sourceClosure (T : Subgroup G) L R z :=
        (equalityClosure (T : Subgroup G) L R z).equivMapOfInjective
          (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective
      calc
        _ = QuotientGroup.mk' (center (sourceClosure (T : Subgroup G) L R z))
            (strictClosureAction (T : Subgroup G) L R z k.val (e u)) := by
          apply congrArg (QuotientGroup.mk' (center (sourceClosure (T : Subgroup G) L R z)))
          apply Subtype.ext
          rfl
        _ = _ := (strictQuotientAction_mk (T : Subgroup G) L R z k.val (e u)).symm)

 theorem LocalAnalysis.strictLiftProjection_isCover
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Representation.OneCohomology.IsCover (strictLiftProjection A h611 hnatural hz horder hstrict) := by
  refine ⟨?_, ?_, A.strictLift_coinvariants_ker h611 hnatural hz horder hstrict⟩
  · intro w
    obtain ⟨v,hv⟩ := strictLiftProjectionHom_surjective (T : Subgroup G) L R z w.toMul
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
  · intro v hv a
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective _ v.toMul
    have hvu : v = Additive.ofMul (QuotientGroup.mk' _ u) := congrArg Additive.ofMul hu.symm
    subst v
    let N := equalityClosure (T : Subgroup G) L R z
    let U := sourceClosure (T : Subgroup G) L R z
    let e : N ≃* U := N.equivMapOfInjective
      (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective
    have hc : e u ∈ center U := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Additive.toMul hv
    have hfix := A.strict_layerClosure_fixes_center h611 hnatural hstrict k.val k.property ⟨e u,hc⟩
    rw [strictLiftRepresentation_mk]
    change Additive.ofMul (equalityQuotientAction _ _ _ _ k.val (QuotientGroup.mk' _ u)) = _
    rw [equalityQuotientAction_mk]
    apply congrArg Additive.ofMul
    apply congrArg (QuotientGroup.mk' _)
    apply e.injective
    exact hfix

 theorem LocalAnalysis.strictLiftProjection_kernel_bound
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    Module.finrank (ZMod 2) (strictLiftProjection A h611 hnatural hz horder hstrict).toLinearMap.ker ≤
      Module.finrank (ZMod 2) (Representation.OneCohomology.H1
        (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) :=
  Representation.OneCohomology.finrank_ker_le_H1_of_cover _
    (A.strictLiftProjection_isCover h611 hnatural hz horder hstrict)

 theorem LocalAnalysis.strict_center_card_of_dual_H1_zero
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (hH1 : Module.finrank (ZMod 2) (Representation.OneCohomology.H1
      (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) = 0) :
    Nat.card (center (sourceClosure (T : Subgroup G) L R z)) = 2 := by
  let N := equalityClosure (T : Subgroup G) L R z
  let U := sourceClosure (T : Subgroup G) L R z
  let e : N ≃* U := N.equivMapOfInjective
    (centralizer ({z} : Set G)).subtype (centralizer ({z} : Set G)).subtype_injective
  let q := QuotientGroup.mk' ((equalityLine z).subgroupOf N)
  let p := strictLiftProjection A h611 hnatural hz horder hstrict
  have hi : Function.Injective p.toLinearMap := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    exact Nat.eq_zero_of_le_zero (hH1 ▸ A.strictLiftProjection_kernel_bound h611 hnatural hz horder hstrict)
  have hcenter : (center U).map U.subtype = zpowers z := by
    apply le_antisymm ?_
      ((A.strict_layer_center_intersection h611 hnatural hz horder hstrict) ▸ inf_le_left)
    rintro x ⟨c,hc,rfl⟩
    have hp : p (Additive.ofMul (q (e.symm c))) = 0 := by
      change Additive.ofMul (strictLiftProjectionHom _ _ _ _ (q (e.symm c))) = 0
      rw [strictLiftProjectionHom_mk]
      change Additive.ofMul (QuotientGroup.mk' (center U) (e (e.symm c))) = 0
      rw [e.apply_symm_apply]
      exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff (N := center U) c).mpr hc)
    have hzq : q (e.symm c) = 1 :=
      congrArg Additive.toMul (hi (hp.trans (map_zero p.toLinearMap).symm))
    have hzmem := (QuotientGroup.eq_one_iff _).mp hzq
    change ((e.symm c).val : G) ∈ zpowers z at hzmem
    have he : ((e.symm c).val : G) = (c : G) := congrArg Subtype.val (e.apply_symm_apply c)
    change (c : G) ∈ zpowers z
    exact he ▸ hzmem
  rw [Nat.card_congr ((center U).equivMapOfInjective U.subtype U.subtype_injective).toEquiv,
    hcenter, Nat.card_zpowers, horder]

 theorem LocalAnalysis.strict_dual_H1_pos_of_center_gt_two
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    (hcenter : 2 < Nat.card (center (sourceClosure (T : Subgroup G) L R z))) :
    0 < Module.finrank (ZMod 2) (Representation.OneCohomology.H1
      (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) := by
  by_contra! h
  have hzH := Nat.eq_zero_of_le_zero h
  have hc := A.strict_center_card_of_dual_H1_zero h611 hnatural hz horder hstrict hzH
  omega

 theorem LocalAnalysis.strict_crossing_dual_H1_pos
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    (hX0 : 1 < Nat.card (strictCrossingCenterImage (T : Subgroup G) L R z d)) :
    0 < Module.finrank (ZMod 2) (Representation.OneCohomology.H1
      (strictLayerRepresentation A h611 hnatural hz horder hstrict).dual) := by
  apply A.strict_dual_H1_pos_of_center_gt_two h611 hnatural hz horder hstrict
  have hc := A.strict_crossing_center_image_card h611 hnatural hz horder hTH hstrict hdres hdH
  omega

end Linear
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
