module
public import Theory.Representation.HermitianTensorThree.PointSection.Sections
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointContainment
public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Construction
public import Theory.SpecificGroups.SL2.Affine.Core

/-!
# Natural and A₅ sections for the original centralizer residual

The actual residual maps onto the point local in the native projective
model. The point-local SL₃ lift and the original field isomorphism give
literal lower-block coordinates, with the complete two-group kernel.
Quotienting that kernel yields the same residual/O₂ ≃ SL₂(4) for both
sections. The conjugate row realizes the natural action on V_z/Z; the
lower corner and the proved Hermitian five-point comparison realize the
A₅ core on V/V_z. Every section map is surjective with its exact kernel.
The natural action also gives the invariant interval needed in 8.2.12.

Source: Aschbacher–Smith H.4.6(4), 8.2.11(2–3), and the first paragraph
of 8.2.12, printed pp.382,722, refs/quasithin.pdf. The Chapter 12 consumer
constructs these maps on the literal chosen orbit, without a section-action
or irreducibility assumption. The ambient closure and exclusion are separate.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]
local instance pointSectionModelBinaryAlgebra : Algebra (ZMod 2) (F 1) := ZMod.algebra _ 2
local instance pointSectionModelBinaryModule : Module (ZMod 2) (Representation.OrthogonalFourMinus.FiniteModel.Space 1) :=
  Module.compHom _ (algebraMap (ZMod 2) (F 1))

/-- Both sections retain the same residual quotient, actual quotient maps,
and original conjugation actions. The second action is the five-point A₅ core. -/
@[expose] def PointSectionActions (V W Z R : Subgroup G) : Prop :=
  ∃ hRV : R ≤ normalizer (V : Set G), ∃ hRW : R ≤ normalizer (W : Set G),
    ∃ eR : (R ⧸ pCore 2 R) ≃* SL(2,E 1),
      ∃ qW : W →* Multiplicative (Fin 2 → E 1),
        Function.Surjective qW ∧ qW.ker = Z.subgroupOf W ∧
        (∀ (r : R) (w : W), qW (W.normalizerMonoidHom (inclusion hRW r) w) =
          Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) (qW w)) ∧
      ∃ qV : V →* Multiplicative (BinaryPermutation.core (Fin 5)),
        Function.Surjective qV ∧ qV.ker = W.subgroupOf V ∧
        ∀ (r : R) (v : V),
          (qV (V.normalizerMonoidHom (inclusion hRV r) v)).toAdd =
            BinaryPermutation.coreRepresentation (Fin 5)
              (Representation.OrthogonalFourMinus.FivePoint.Construction.comparison.groupEquiv
                (eR (QuotientGroup.mk' (pCore 2 R) r))).val (qV v).toAdd

/-- A literal point-local cover constructs both source section actions. -/
theorem marked_point_local_sections
    (V W Z R : Subgroup G) [IsElementaryAbelian 2 V]
    (hWV : W ≤ V) (hRV : R ≤ normalizer (V : Set G))
    (hRW : R ≤ normalizer (W : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (p : R →* Matrix.PSL3.LinearThree.pointLocalSL (E 1))
    (hp : Function.Surjective p) (hk : IsPGroup 2 p.ker)
    (he : ∀ (r : R) v, e (Additive.ofMul (V.normalizerMonoidHom (inclusion hRV r) v)) =
      binaryActionHom 1 (p r).val (e (Additive.ofMul v)))
    (hW : ∀ v : Additive V, (v.toMul : G) ∈ W ↔ e v ∈ PointSection.moved)
    (hZ : ∀ v : Additive V, (v.toMul : G) ∈ Z ↔ e v ∈ PointSection.line) :
    PointSectionActions V W Z R := by
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let A := Matrix.PSL3.LinearThree.pointLocalAffineEquiv (E 1)
  let f := A.toMonoidHom.comp p
  have hf : Function.Surjective f := A.surjective.comp hp
  have hkf : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ A.injective]
  let eR := (f.pCoreQuotientEquiv hf hkf).trans (Matrix.SL2.affineCoreQuotientEquiv (E 1))
  have heR (r : R) : eR (QuotientGroup.mk' (pCore 2 R) r) = (A (p r)).right := rfl
  let i := (inclusion hWV).toAdditive.toZModLinearMap 2
  let qW : W →* Multiplicative (Fin 2 → E 1) :=
    (PointSection.conjugateRow.comp (e.toLinearMap.comp i)).toAddMonoidHom.toMultiplicative
  have hqW : Function.Surjective qW := by
    intro v
    obtain ⟨X,hX⟩ := PointSection.conjugateRow_surjective v.toAdd
    let x := e.symm X.val
    have hx : (x.toMul : G) ∈ W := (hW x).mpr (by rw [e.apply_symm_apply]; exact X.property)
    refine ⟨⟨x.toMul,hx⟩,?_⟩
    change PointSection.conjugateRow (e x) = v.toAdd
    rw [e.apply_symm_apply]
    exact hX
  have hqWker : qW.ker = Z.subgroupOf W := by
    ext w
    change PointSection.conjugateRow (e (i (Additive.ofMul w))) = 0 ↔ (w : G) ∈ Z
    rw [PointSection.conjugateRow_kernel
      ⟨e (i (Additive.ofMul w)),(hW _).mp w.property⟩]
    exact (hZ _).symm
  have hqWact (r : R) (w : W) :
      qW (W.normalizerMonoidHom (inclusion hRW r) w) =
        Matrix.SL2.naturalAction (E 1) (eR (QuotientGroup.mk' (pCore 2 R) r)) (qW w) := by
    apply Multiplicative.toAdd.injective
    change PointSection.conjugateRow (e (Additive.ofMul
      (V.normalizerMonoidHom (inclusion hRV r) (inclusion hWV w)))) = _
    rw [he,heR]
    exact (PointSection.point_local_sections (p r)).1
      ⟨e (Additive.ofMul (inclusion hWV w)),(hW _).mp w.property⟩
  let c := Representation.OrthogonalFourMinus.FivePoint.Construction.comparison
  let qV : V →* Multiplicative (BinaryPermutation.core (Fin 5)) :=
    (c.coordinates.toLinearMap.comp (PointSection.lowerCorner.comp e.toLinearMap)).toAddMonoidHom.toMultiplicative
  have hqV : Function.Surjective qV := by
    intro v
    obtain ⟨X,hX⟩ := PointSection.lowerCorner_surjective (c.coordinates.symm v.toAdd)
    refine ⟨(e.symm X).toMul,?_⟩
    change c.coordinates (PointSection.lowerCorner (e (e.symm X)))=v.toAdd
    rw [e.apply_symm_apply,hX,c.coordinates.apply_symm_apply]
  have hqVker : qV.ker = W.subgroupOf V := by
    ext v
    change c.coordinates (PointSection.lowerCorner (e (Additive.ofMul v)))=0 ↔ (v : G) ∈ W
    rw [LinearEquiv.map_eq_zero_iff,PointSection.lowerCorner_kernel]
    exact (hW _).symm
  refine ⟨hRV,hRW,eR,qW,hqW,hqWker,hqWact,qV,hqV,hqVker,?_⟩
  intro r v
  change c.coordinates (PointSection.lowerCorner (e (Additive.ofMul
    (V.normalizerMonoidHom (inclusion hRV r) v)))) = _
  rw [he,(PointSection.point_local_sections (p r)).2,c.intertwines,heR]
  rfl

/-- The original residual has a literal point-local lift, through the
native projective group and the fixed field transport. Its whole kernel is a two-group. -/
theorem marked_point_residual_lift
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    ∃ p : Centralizer.localResidual L z →* Matrix.PSL3.LinearThree.pointLocalSL (E 1),
      Function.Surjective p ∧ IsPGroup 2 p.ker ∧
      ∀ (r : Centralizer.localResidual L z) v,
        e (Additive.ofMul (V.normalizerMonoidHom (inclusion
          (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r) v)) =
          binaryActionHom 1 (p r).val (e (Additive.ofMul v)) := by
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp hq
  have hkf : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective]
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hP := marked_point_centralizer_preimage V L hLN e q he z hz
  have hRI := (point_residual_images L (z : G) f hf hkf hP).1
  rw [Matrix.PSL3Four.ElementaryParabolic.native_parabolic_eq_local] at hRI
  let P := Matrix.PSL3.LinearThree.OuterExtensions.localFactor Matrix.PSL3Four.F true
  let fR : R →* P := (f.comp (inclusion hRL)).codRestrict P
    (fun r => hRI.le (mem_map_of_mem f (show inclusion hRL r ∈ R.subgroupOf L from r.property)))
  have hfR : Function.Surjective fR := by
    intro y
    obtain ⟨l,hl,hy⟩ := hRI.ge y.property
    exact ⟨⟨l,hl⟩,Subtype.ext hy⟩
  have hkR : IsPGroup 2 fR.ker := by
    rw [MonoidHom.ker_codRestrict,←MonoidHom.comap_ker]
    exact hkf.comap_of_injective _ (inclusion_injective hRL)
  let k := Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num)
  let d : P ≃* Matrix.PSL3.LinearThree.pointLocalSL (E 1) :=
    (Matrix.PSL3.LinearThree.pointLocalProjectEquiv Matrix.PSL3Four.F).symm.trans
      (Matrix.PSL3.LinearThree.pointLocalSLFieldEquiv k)
  let p := d.toMonoidHom.comp fR
  refine ⟨p,d.surjective.comp hfR,?_,?_⟩
  · rwa [MonoidHom.ker_comp_of_injective _ _ d.injective]
  · intro r v
    have heq : (q (inclusion hRL r)).val = binaryActionHom 1 (p r).val := by
      let a := (Matrix.PSL3.LinearThree.pointLocalProjectEquiv Matrix.PSL3Four.F).symm (fR r)
      have ha : (QuotientGroup.mk' _ a.val : Matrix.PSL3Four.PSL) = f (inclusion hRL r) :=
        congrArg Subtype.val ((Matrix.PSL3.LinearThree.pointLocalProjectEquiv Matrix.PSL3Four.F).apply_symm_apply (fR r))
      have hm := nativeBinaryEquiv_mk a.val
      rw [ha] at hm
      change (nativeBinaryEquiv (nativeBinaryEquiv.symm (q (inclusion hRL r)))).val = _ at hm
      rw [nativeBinaryEquiv.apply_symm_apply] at hm
      exact hm
    exact (he (inclusion hRL r) (Additive.ofMul v)).trans (congrArg (fun a => a (e (Additive.ofMul v))) heq)

theorem marked_point_residual_sections
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    PointSectionActions V (Centralizer.commutatorSpace L V z) (zpowers (z : G))
      (Centralizer.localResidual L z) := by
  let f := nativeBinaryEquiv.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp hq
  have hfk : IsPGroup 2 f.ker := by
    rwa [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective]
  have hP := marked_point_centralizer_preimage V L hLN e q he z hz
  have hXimage := (point_residual_images L (z : G) f hf hfk hP).2
  let X := Centralizer.localTwoCore L z
  have hXL : X ≤ L := (Centralizer.localTwoCore_le L z).trans
    ((Centralizer.localResidual_le L z).trans inf_le_left)
  let r := (binaryImage 1).subtype.comp (q.comp (inclusion hXL))
  have hRange : r.range = UnipotentRadicals.point 1 := by
    have hm := congrArg (Subgroup.map ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom)) hXimage
    rw [map_map,native_point_root_image] at hm
    have heq : ((binaryImage 1).subtype.comp nativeBinaryEquiv.toMonoidHom).comp f =
        (binaryImage 1).subtype.comp q := by
      apply MonoidHom.ext
      intro l
      exact congrArg Subtype.val (nativeBinaryEquiv.apply_symm_apply (q l))
    rw [heq] at hm
    have hi : (inclusion hXL).range = X.subgroupOf L := by
      ext l
      constructor
      · rintro ⟨x,rfl⟩
        exact x.property
      · intro hl
        exact ⟨⟨l,hl⟩,Subtype.ext rfl⟩
    change (((binaryImage 1).subtype.comp q).comp (inclusion hXL)).range = _
    rw [MonoidHom.range_comp,hi]
    exact hm
  let R := Centralizer.localResidual L z
  have hRL : R ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hRV : R ≤ normalizer (V : Set G) := hRL.trans hLN
  have hRW : R ≤ normalizer (Centralizer.commutatorSpace L V z : Set G) :=
    (point_commutator_normalizes L V R z (hRL.trans L.le_normalizer) hRV
      ((Centralizer.localResidual_le L z).trans inf_le_right)).2
  obtain ⟨p,hp,hkp,hep⟩ := marked_point_residual_lift V L hLN e q he hq hk z hz
  exact marked_point_local_sections V (Centralizer.commutatorSpace L V z) (zpowers (z : G)) R
    (Centralizer.commutatorSpace_le L V z hLN) hRV hRW e p hp hkp hep
    (marked_point_commutator_coordinates V X (hXL.trans hLN) e r
      (fun x v => he (inclusion hXL x) v) hRange)
    (fun v => (marked_point_line V e z hz v).symm)

omit [Finite G] in
/-- The natural quotient is irreducible for the literal original residual.
This is the invariant-section assertion used at the start of 8.2.12. -/
theorem PointSectionActions.natural_interval
    (V W Z R : Subgroup G) (h : PointSectionActions V W Z R)
    (U : Subgroup G) (hZU : Z ≤ U) (hUW : U ≤ W)
    (hRU : R ≤ normalizer (U : Set G)) : U = Z ∨ U = W := by
  obtain ⟨hRV,hRW,eR,qW,hqW,hker,hact,_⟩ := h
  let B := (U.subgroupOf W).map qW
  have hB : ∀ g v, v ∈ B → Matrix.SL2.naturalAction (E 1) g v ∈ B := by
    intro g v hv
    obtain ⟨r,hr⟩ := (eR.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 R))) g
    change eR (QuotientGroup.mk' (pCore 2 R) r) = g at hr
    obtain ⟨w,hw,rfl⟩ := hv
    rw [←hr,←hact]
    exact mem_map_of_mem qW
      ((le_normalizer_iff.mp hRU r r.property w hw) :
        W.normalizerMonoidHom (inclusion hRW r) w ∈ U.subgroupOf W)
  rcases Matrix.SL2.naturalAction_irreducible (E 1) B hB with hbot|htop
  · left
    apply le_antisymm ?_ hZU
    intro u hu
    have hh : qW ⟨u,hUW hu⟩ ∈ B := mem_map_of_mem qW hu
    rw [hbot,mem_bot] at hh
    have hk : (⟨u,hUW hu⟩ : W) ∈ qW.ker := hh
    exact (hker ▸ hk : (⟨u,hUW hu⟩ : W) ∈ Z.subgroupOf W)
  · right
    apply le_antisymm hUW
    intro w hw
    have hmem : qW ⟨w,hw⟩ ∈ B := htop.ge (mem_top _)
    obtain ⟨u,hu,he⟩ := hmem
    have hk : (⟨w,hw⟩ : W)*u⁻¹ ∈ qW.ker := by
      change qW ((⟨w,hw⟩ : W)*u⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hz : w*(u : G)⁻¹ ∈ Z := (hker ▸ hk : (⟨w,hw⟩ : W)*u⁻¹ ∈ Z.subgroupOf W)
    have hh := U.mul_mem (hZU hz) hu
    change (w*(u : G)⁻¹)*(u : G) ∈ U at hh
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
