module
public import Theory.Representation.HermitianTensorThree.PointSection.Movement
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCore
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.TwoFixedLinesIrreducible

/-!
# The original point-local five-space

The literal residual and its full two-core map to the point parabolic
and root plane. Equivariance sends the subgroup commutator to the native
five-dimensional displacement span, so the original V_z has order 32.
The source Sylow normalizes this subgroup; its fixed-point theorem forces
the unique central involution into it. Cardinalities then give the strict
L_z T-invariant series 1 < Z < V_z < V.

Source: Aschbacher–Smith 8.2.11(2), printed p.722, refs/quasithin.pdf.
The natural action on V_z/Z and the action on V/V_z are separate obligations.
The Chapter 12 application discharges the coordinate and fixed-line inputs
on the actual chosen module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Equivariant point coordinates compute the original subgroup commutator. -/
theorem marked_point_commutator_card
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1)
    (q : X →* (Space 1 ≃ₗ[ZMod 2] Space 1))
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) = q x (e v))
    (hq : q.range = UnipotentRadicals.point 1) : Nat.card (⁅V,X⁆ : Subgroup G) = 32 := by
  let f := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hXV)
  let ρ := (automizerRepresentation V).comp f
  let σ := UnipotentRadicals.ambientAction 1
  have hact (x : X) (v : V) :
      ρ x (Additive.ofMul v) = Additive.ofMul
        (⟨(x : G)*(v : G)*(x : G)⁻¹,le_normalizer_iff.mp hXV x x.property v v.property⟩ : V) := rfl
  have hcomm := commutator_image_eq ρ V V X hXV le_rfl (MonoidHom.id X)
    (MonoidHom.id V) (fun x v => hact x v) ⊤ (by
      ext v
      simp [binarySubgroup])
  have hC : (⁅V,X⁆).subgroupOf V = binarySubgroup (subspaceCommutator ρ ⊤ (⊤ : Subgroup X)) := by
    simpa only [map_id,(MonoidHom.id X).range_eq_top_of_surjective (fun x => ⟨x,rfl⟩)] using hcomm
  have he' (x : X) (w : Space 1) : ρ x (e.symm w) = e.symm (σ (q x) w) := by
    apply e.injective
    exact (he x (e.symm w)).trans (by simp only [e.apply_symm_apply]; rfl)
  have hm := subspaceCommutator_map_embedding ρ σ q e.symm.toLinearMap he'
    (⊤ : Subgroup X) (⊤ : Submodule (ZMod 2) (Space 1))
  have hM : subspaceCommutator ρ ⊤ (⊤ : Subgroup X) = PointSection.moved.map e.symm.toLinearMap := by
    dsimp only [σ] at hm
    simpa only [Submodule.map_top,LinearEquiv.range,←MonoidHom.range_eq_map,hq,
      PointSection.point_commutator] using hm
  have hle : ⁅V,X⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hXV
  calc
    Nat.card (⁅V,X⁆ : Subgroup G) = Nat.card ((⁅V,X⁆).subgroupOf V) :=
      (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).symm
    _ = Nat.card (binarySubgroup (PointSection.moved.map e.symm.toLinearMap)) := by rw [hC,hM]
    _ = Nat.card (PointSection.moved.map e.symm.toLinearMap) := binarySubgroup_card _
    _ = Nat.card PointSection.moved :=
      (Nat.card_congr (PointSection.moved.equivMapOfInjective e.symm.toLinearMap e.symm.injective).toEquiv).symm
    _ = 32 := PointSection.card_moved

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

/-- The marked original point-local residual has commutator space of order 32. -/
theorem marked_point_residual_commutator_card
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    Nat.card (Centralizer.commutatorSpace L V z) = 32 := by
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
  exact marked_point_commutator_card V X (hXL.trans hLN) e r
    (fun x v => he (inclusion hXL x) v) hRange


omit [Finite G] in
/-- The original Sylow normalizes the centralizer residual and its commutator. -/
theorem point_commutator_normalizes
    (L V T : Subgroup G) (z : G)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V : Set G))
    (hTz : T ≤ centralizer ({z} : Set G)) :
    T ≤ normalizer (Centralizer.localResidual L z : Set G) ∧
      T ≤ normalizer (Centralizer.commutatorSpace L V z : Set G) := by
  have hR : T ≤ normalizer (Centralizer.localResidual L z : Set G) := by
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    exact (le_inf hTL (hTz.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hX : T ≤ normalizer (Centralizer.localTwoCore L z : Set G) :=
    hR.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  refine ⟨hR,?_⟩
  intro t ht
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅V,Centralizer.localTwoCore L z⁆).map (MulAut.conj t).toMonoidHom = _
  have hv : V.map (MulAut.conj t).toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hTV ht)
  have hx : (Centralizer.localTwoCore L z).map (MulAut.conj t).toMonoidHom =
      Centralizer.localTwoCore L z := mem_normalizer_iff_map_conj_eq.mp (hX ht)
  rw [map_commutator,hv,hx]
  rfl

/-- The actual five-space lies strictly between the central line and V. -/
theorem point_commutator_strict_series
    (L V T : Subgroup G) [IsElementaryAbelian 2 V] (z : G)
    (hLN : L ≤ normalizer (V : Set G))
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V : Set G))
    (hT : IsPGroup 2 T) (hTz : T ≤ centralizer ({z} : Set G))
    (hzo : orderOf z = 2) (hfix : V ⊓ centralizer (T : Set G) = zpowers z)
    (hVcard : Nat.card V = 512) (hWcard : Nat.card (Centralizer.commutatorSpace L V z) = 32) :
    ⊥ < zpowers z ∧ zpowers z < Centralizer.commutatorSpace L V z ∧
      Centralizer.commutatorSpace L V z < V ∧
      Centralizer.localResidual L z ⊔ T ≤ normalizer (Centralizer.commutatorSpace L V z : Set G) := by
  let W := Centralizer.commutatorSpace L V z
  have hWV : W ≤ V := Centralizer.commutatorSpace_le L V z hLN
  have hTW := (point_commutator_normalizes L V T z hTL hTV hTz).2
  have hWne : W ≠ ⊥ := (one_lt_card_iff_ne_bot W).mp (by rw [hWcard]; decide)
  have hzW : z ∈ W := involution_mem_of_invariant_of_fixed_line T W V z hzo hT
    ((IsElementaryAbelian.isPGroup 2 V).to_le hWV) hTW hWne hWV hfix
  have hZcard : Nat.card (zpowers z) = 2 := (Nat.card_zpowers z).trans hzo
  have hRL : Centralizer.localResidual L z ≤ L := (Centralizer.localResidual_le L z).trans inf_le_left
  have hRW := (point_commutator_normalizes L V (Centralizer.localResidual L z) z
    (hRL.trans L.le_normalizer) (hRL.trans hLN)
    ((Centralizer.localResidual_le L z).trans inf_le_right)).2
  refine ⟨bot_lt_iff_ne_bot.mpr ((one_lt_card_iff_ne_bot _).mp (by rw [hZcard]; decide)),
    lt_of_le_of_ne (zpowers_le.mpr hzW) ?_,lt_of_le_of_ne hWV ?_,sup_le hRW hTW⟩
  · intro he
    have hh := congrArg (fun K : Subgroup G => Nat.card K) he
    rw [hZcard,hWcard] at hh
    contradiction
  · intro he
    have hh := congrArg (fun K : Subgroup G => Nat.card K) he
    rw [hWcard,hVcard] at hh
    contradiction

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
