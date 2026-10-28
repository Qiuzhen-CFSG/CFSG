module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Restriction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualGeneration
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.CoreGeometry
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.Quotient

/-!
# The intrinsic point-residual core in the natural split A₆ block

The centralizer of the duad vector 45 projects to its actual A₆ point
stabilizer. The two-residual projects to the A₄ fixing 4 and 5, and its
translation part is exactly the perpendicular hyperplane: the invariant
point functional gives the upper bound and the established residual
commutator generation gives the reverse containment. Prime-core transport
through the elementary translation kernel then identifies the intrinsic
residual core with the hyperplane and the actual Klein four, of order 32.

Source application: the original subgroup U in Aschbacher–Smith 14.3.19(10),
printed p.997. All centralizers, residuals, cores and subgroup maps retain
the literal point in the natural split model.
-/

@[expose] public section
open Subgroup SemidirectProduct
open scoped commutatorElement
namespace BinaryPermutation.SixNaturalSplit
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

noncomputable def canonicalPoint : Model := inl (Multiplicative.ofAdd (pairVector 4 5))
noncomputable def canonicalCore : Subgroup Model :=
  ((pResidual 2 (centralizer ({canonicalPoint} : Set Model))).map
    (centralizer ({canonicalPoint} : Set Model)).subtype).pCoreIn 2

noncomputable def actorMap : Model →* Equiv.Perm (Fin 6) :=
  Actor.subtype.comp rightHom
noncomputable def pointCentralizer : Subgroup Model := L1.comap actorMap
noncomputable def pointResidual : Subgroup Model :=
  (pResidual 2 pointCentralizer).map pointCentralizer.subtype

theorem fixed_point_iff (g : Actor) :
    naturalRepresentation (Fin 6) g.val (pairVector 4 5) = pairVector 4 5 ↔ g.val ∈ L1 := by
  rw [pairVector_map, pairVector_eq_iff (g.val.injective.ne (by decide)) (by decide)]
  change Theory.SpecificGroups.SymmetricSix.pair (g.val 4) (g.val 5) =
    Theory.SpecificGroups.SymmetricSix.pair 4 5 ↔ g.val ∈ H1 ∧ g.val ∈ alternatingGroup (Fin 6)
  rw [and_iff_left g.property]
  change _ ↔ (Theory.SpecificGroups.SymmetricSix.pair 4 5).image g.val = _
  simp only [Theory.SpecificGroups.SymmetricSix.pair, Finset.image_insert, Finset.image_singleton]

theorem pointCentralizer_eq : pointCentralizer = centralizer ({canonicalPoint} : Set Model) := by
  ext x
  rw [mem_centralizer_singleton_iff]
  rw [eq_comm]
  change x.right.val ∈ L1 ↔ canonicalPoint * x = x * canonicalPoint
  constructor
  · intro hx
    apply SemidirectProduct.ext
    · simp only [canonicalPoint, mul_left, left_inl, right_inl, map_one, MulAut.one_apply]
      change Multiplicative.ofAdd (pairVector 4 5) * x.left =
        x.left * action x.right (Multiplicative.ofAdd (pairVector 4 5))
      rw [mul_comm]
      congr 1
      exact (Multiplicative.toAdd.injective ((fixed_point_iff x.right).mpr hx)).symm
    · simp [canonicalPoint]
  · intro hx
    have hh := congrArg SemidirectProduct.left hx
    simp only [canonicalPoint, mul_left, left_inl, right_inl, map_one, MulAut.one_apply] at hh
    change Multiplicative.ofAdd (pairVector 4 5) * x.left =
      x.left * action x.right (Multiplicative.ofAdd (pairVector 4 5)) at hh
    rw [mul_comm] at hh
    exact (fixed_point_iff x.right).mp (congrArg Multiplicative.toAdd (mul_left_cancel hh).symm)

noncomputable def pointProjection : pointCentralizer →* L1 :=
  (actorMap.comp pointCentralizer.subtype).codRestrict L1 (fun x => x.property)
noncomputable def pointSection : L1 →* pointCentralizer :=
  ((inr : Actor →* Model).comp
    (L1.subtype.codRestrict Actor (fun x => x.property.2))).codRestrict
      pointCentralizer (fun x => x.property)

theorem pointProjection_surjective : Function.Surjective pointProjection := by
  intro g
  exact ⟨pointSection g, rfl⟩

theorem residual_actor_image : pointResidual.map actorMap = K := by
  rw [pointResidual, map_map]
  change (pResidual 2 pointCentralizer).map (L1.subtype.comp pointProjection) = K
  rw [← map_map, map_pResidual_of_surjective 2 pointProjection pointProjection_surjective,
    residual_L1]

theorem inr_mem_residual (g : Actor) (hg : g.val ∈ K) : (inr g : Model) ∈ pointResidual := by
  rw [← residual_L1] at hg
  obtain ⟨a,ha,he⟩ := hg
  have h := map_pResidual_le 2 pointSection (mem_map_of_mem pointSection ha)
  have hh := mem_map_of_mem pointCentralizer.subtype h
  have hv : pointCentralizer.subtype (pointSection a) = (inr g : Model) :=
    congrArg (inr : Actor → Model) (Subtype.ext he)
  exact hv ▸ hh

theorem point_functional_invariant (g : Actor) (hg : g.val ∈ L1)
    (v : natural (Fin 6)) :
    form (pairVector 4 5) (naturalRepresentation (Fin 6) g.val v) = form (pairVector 4 5) v := by
  have h := form_invariant g.val (pairVector 4 5) v
  rwa [(fixed_point_iff g).mpr hg] at h

noncomputable def pointFunctional : pointCentralizer →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (form (pairVector 4 5) x.val.left.toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change form (pairVector 4 5) 0 = 0
    exact map_zero _
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change form (pairVector 4 5)
      (x.val.left.toAdd + naturalRepresentation (Fin 6) x.val.right.val y.val.left.toAdd) = _
    rw [map_add, point_functional_invariant x.val.right (show x.val.right.val ∈ L1 from x.property)]
    rfl

theorem mem_hyperplane_iff (v : natural (Fin 6)) :
    v ∈ PointAction.Hyperplane ↔ form (pairVector 4 5) v = 0 := by
  constructor
  · intro h
    exact h (pairVector 4 5) (Submodule.subset_span (by simp))
  · intro h w hw
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [h]

theorem residual_left_mem (x : Model) (hx : x ∈ pointResidual) :
    x.left.toAdd ∈ PointAction.Hyperplane := by
  obtain ⟨x,hx,rfl⟩ := hx
  apply (mem_hyperplane_iff _).mpr
  have hp : IsPGroup 2 (Multiplicative (ZMod 2)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card]; rfl)
  exact congrArg Multiplicative.toAdd (pResidual_le_ker_of_isPGroup 2 pointFunctional hp hx)

theorem residual_normalized : pointCentralizer ≤ normalizer (pointResidual : Set Model) :=
  pointCentralizer.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image pointCentralizer (pResidual 2 pointCentralizer))

theorem canonical_generation : PointAction.Hyperplane ≤
    Representation.BinaryOffender.subspaceCommutator (naturalRepresentation (Fin 6))
      PointAction.Hyperplane K := by
  have he : Representation.BinaryOffender.subspaceStabilizer (naturalRepresentation (Fin 6))
      canonicalLine = H1 := by
    ext g
    rw [mem_stabilizer_iff_map, canonicalLine_stabilizer]
  have hh := NaturalResidualGeneration.point_residual_generates
    (alternatingGroup (Fin 6)) le_rfl canonicalLine canonicalLine_finrank
  dsimp only at hh
  rw [he, inf_comm] at hh
  change PointAction.Hyperplane ≤ Representation.BinaryOffender.subspaceCommutator
    (naturalRepresentation (Fin 6)) PointAction.Hyperplane ((pResidual 2 L1).map L1.subtype) at hh
  rwa [residual_L1] at hh

theorem inl_hyperplane_mem_residual (v : natural (Fin 6)) (hv : v ∈ PointAction.Hyperplane) :
    (inl (Multiplicative.ofAdd v) : Model) ∈ pointResidual := by
  let D : Submodule (ZMod 2) (natural (Fin 6)) :=
    AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
      (pointResidual.comap (inl : Vector →* Model)))
  have hD : Representation.BinaryOffender.subspaceCommutator (naturalRepresentation (Fin 6))
      PointAction.Hyperplane K ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,w,hw,rfl⟩
    let a : Actor := ⟨g,hg.2⟩
    have hi := inr_mem_residual a hg
    have hvC : (inl (Multiplicative.ofAdd w) : Model) ∈ pointCentralizer := by
      change (1 : Equiv.Perm (Fin 6)) ∈ L1
      exact one_mem _
    have hc := le_normalizer_iff_commutator_le_left.mp residual_normalized
      (commutator_mem_commutator hi hvC)
    change (inl (Multiplicative.ofAdd (naturalRepresentation (Fin 6) g w - w)) : Model) ∈ pointResidual
    convert hc using 1
    rw [commutatorElement_def, ← map_inv, ← inl_aut]
    change inl _ = inl _ * (inl _)⁻¹
    rw [← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    exact sub_eq_add_neg _ _
  exact hD (canonical_generation hv)

theorem residual_coordinates (x : Model) : x ∈ pointResidual ↔
    x.left.toAdd ∈ PointAction.Hyperplane ∧ x.right.val ∈ K := by
  constructor
  · intro hx
    exact ⟨residual_left_mem x hx, residual_actor_image ▸ mem_map_of_mem actorMap hx⟩
  · rintro ⟨hv,hg⟩
    have h := pointResidual.mul_mem (inl_hyperplane_mem_residual x.left.toAdd hv)
      (inr_mem_residual x.right hg)
    change inl x.left * inr x.right ∈ pointResidual at h
    rwa [inl_left_mul_inr_right] at h

theorem actorMap_ker : actorMap.ker = translations := by
  ext x
  change actorMap x = 1 ↔ ∃ v : Vector, inl v = x
  constructor
  · intro hx
    have hr : x.right = 1 := Subtype.ext hx
    refine ⟨x.left, ?_⟩
    exact SemidirectProduct.ext rfl hr.symm
  · rintro ⟨v,rfl⟩
    rfl

theorem actorMap_ker_two : IsPGroup 2 actorMap.ker := by
  rw [actorMap_ker, translations_eq_twoCore]
  exact pCore_isPGroup

theorem canonicalCore_eq : canonicalCore = pointResidual.pCoreIn 2 := by
  rw [canonicalCore, ← pointCentralizer_eq]
  rfl

theorem canonicalCore_actor_image : canonicalCore.map actorMap = pointCoreEven := by
  rw [canonicalCore_eq, map_pCoreIn_of_ker_isPGroup actorMap actorMap_ker_two,
    residual_actor_image, K_core_eq_pointCoreEven]

theorem canonicalCore_coordinates (x : Model) : x ∈ canonicalCore ↔
    x.left.toAdd ∈ PointAction.Hyperplane ∧ x.right.val ∈ pointCoreEven := by
  constructor
  · intro hx
    have hxR : x ∈ pointResidual := (pCoreIn_le 2 pointResidual) (canonicalCore_eq ▸ hx)
    exact ⟨residual_left_mem x hxR, canonicalCore_actor_image ▸ mem_map_of_mem actorMap hx⟩
  · rintro ⟨hv,hg⟩
    have hxR : x ∈ pointResidual := (residual_coordinates x).mpr ⟨hv,pointCoreEven_le_K hg⟩
    let f := actorMap.subgroupMap pointResidual
    have hk : IsPGroup 2 f.ker := by
      rw [Subgroup.ker_subgroupMap]
      exact actorMap_ker_two.comap_subtype
    have he := f.comap_pCore_of_ker_isPGroup (actorMap.subgroupMap_surjective pointResidual) hk
    have hm : actorMap x ∈ (pointResidual.map actorMap).pCoreIn 2 := by
      rw [residual_actor_image,K_core_eq_pointCoreEven]
      exact hg
    obtain ⟨y,hy,hyx⟩ := hm
    have hyf : y = f ⟨x,hxR⟩ := Subtype.ext hyx
    have hxx : (⟨x,hxR⟩ : pointResidual) ∈ pCore 2 pointResidual := by
      rw [← he]
      change f ⟨x,hxR⟩ ∈ pCore 2 (pointResidual.map actorMap)
      exact hyf ▸ hy
    rw [canonicalCore_eq]
    exact mem_map_of_mem pointResidual.subtype hxx

noncomputable def canonicalCoreCoordinates : canonicalCore ≃
    (Multiplicative PointAction.Hyperplane × pointCoreEven) where
  toFun x := (Multiplicative.ofAdd ⟨x.val.left.toAdd,((canonicalCore_coordinates x.val).mp x.property).1⟩,
    ⟨x.val.right.val,((canonicalCore_coordinates x.val).mp x.property).2⟩)
  invFun x := ⟨⟨Multiplicative.ofAdd x.1.toAdd.val,⟨x.2.val,x.2.property.2⟩⟩,
    (canonicalCore_coordinates _).mpr ⟨x.1.toAdd.property,x.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem canonicalCore_card : Nat.card canonicalCore = 32 := by
  rw [Nat.card_congr canonicalCoreCoordinates,Nat.card_prod,PointAction.hyperplane_card,
    pointCoreEven_card]


end BinaryPermutation.SixNaturalSplit
