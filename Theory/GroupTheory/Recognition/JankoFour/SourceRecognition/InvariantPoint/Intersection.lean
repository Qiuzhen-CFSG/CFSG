module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Core
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Transversality
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.CocodeImage

/-!
# The invariant core preimage is transverse to the original cocode

The original cocode image is the pointwise hexad translation group.
Its regular action on the sixteen complementary points transports a fixed
vector in one point space into all sixteen point spaces, using the same
design conjugator that aligns the original cubic marking. Three distinct
point spaces intersect trivially, so that vector vanishes.

An element in the original cocode subgroup centralizes that subgroup.
Applying the fixed-vector argument to its actual Q/Z(Q) image proves that
the constructed invariant elementary subgroup meets Q intersect E exactly
in Z(Q). This removes the last invariant-preimage premise in ToddSplitting;
the original Mathieu PointData application is in PointData.lean.

Source: Aschbacher--Segev (4.8), Invent. Math. 105 (1991), p.599,
DOI 10.1007/BF01232280. All quotient actions and both native/original
markings are the established literal maps.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup LocalGeometry LocalGeometry.LocalSubgroups Sporadic.Mathieu M22TripleCover M22ValueBound.Concrete
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e)) [IsExtraspecial 2 (core z)]

/-- A common fixed vector in an outside point space vanishes, using the
literal original hexad translations and the same design conjugator. -/
theorem original_point_fixed_eq_zero
    (U : Subgroup (centralizer z)) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hU : U.map (designAutEquiv.symm.toMonoidHom.comp (CubicLift.projection e)) =
      (m22HexadPointwiseKernel B).map inclusion)
    (p : Fin 22) (hp : p ∉ B) (b : m22DesignAut)
    (hb : ∀ j : centralizer z,
      pointAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) j)) =
        b.val * (designAutEquiv.symm (CubicLift.projection e j)).val * b.val⁻¹)
    (v : BinarySpace) (hv : v ∈ pointSpace (b • p))
    (hfix : ∀ u ∈ U,
      M22TripleCover.Ambient.binaryAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) u)) v=v) :
    v=0 := by
  have hall (q : Fin 22) (hq : q ∉ B) : v ∈ pointSpace (b • q) := by
    obtain ⟨a,ha⟩ := (m22HexadKernel_regular hB hp).surjective ⟨q,hq⟩
    have ham : inclusion a.val.val ∈ (m22HexadPointwiseKernel B).map inclusion :=
      mem_map_of_mem _ ⟨a.val,a.property,rfl⟩
    rw [←hU] at ham
    obtain ⟨u,hu,he⟩ := ham
    have huq : (designAutEquiv.symm (CubicLift.projection e u)) • p=q := by
      change designAutEquiv.symm (CubicLift.projection e u)=inclusion a.val.val at he
      rw [he]
      exact congrArg Subtype.val ha
    have hh := pointSpace_transport (coreAmbientHom h e X (QuotientGroup.mk' (core z) u))
      (b • p) v hv
    rw [hfix u hu,hb] at hh
    have hpoint : (b.val * (designAutEquiv.symm (CubicLift.projection e u)).val * b.val⁻¹) (b • p)=b • q := by
      change (b * designAutEquiv.symm (CubicLift.projection e u) * b⁻¹) • (b • p)=b • q
      rw [mul_smul,mul_smul,inv_smul_smul,huq]
    rwa [hpoint] at hh
  have hc : Bᶜ.card=16 := by
    rw [Finset.card_compl,m22Block_card B hB]
    rfl
  obtain ⟨q,hq,hqp⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({p} : Finset (Fin 22)).card < Bᶜ.card by rw [Finset.card_singleton,hc]; decide)
  have hqp' : q≠p := by simpa using hqp
  obtain ⟨r,hr,hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({p,q} : Finset (Fin 22)).card < Bᶜ.card by
      rw [Finset.card_pair hqp'.symm,hc]; decide)
  have hrp : r≠p := fun he => hrpq (by simp [he])
  have hrq : r≠q := fun he => hrpq (by simp [he])
  exact pointSpace_triple_eq_zero (b • p) (b • q) (b • r)
    (fun he => hqp' (MulAction.injective b he).symm)
    (fun he => hrp (MulAction.injective b he).symm)
    (fun he => hrq (MulAction.injective b he).symm)
    v hv (hall q (Finset.mem_compl.mp hq)) (hall r (Finset.mem_compl.mp hr))

omit [IsExtraspecial 2 (core z)] in
include h X in
/-- The actual elementary preimage is transverse to the original cocode
intersection, with the original marker as the full intersection. -/
theorem exists_original_pointCore_transverse
    (U J : Subgroup (centralizer z)) [IsElementaryAbelian 2 U]
    (hZU : center (centralizer z) ≤ U)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hU : U.map (designAutEquiv.symm.toMonoidHom.comp (CubicLift.projection e)) =
      (m22HexadPointwiseKernel B).map inclusion)
    (p : Fin 22) (hp : p ∉ B)
    (hJ : ∀ j ∈ J, (designAutEquiv.symm (CubicLift.projection e j)) • p=p) :
    ∃ P : Subgroup (centralizer z), P ≤ core z ∧ IsElementaryAbelian 2 P ∧
      Nat.card P=128 ∧ center (centralizer z) ≤ P ∧
      J ≤ normalizer (P : Set (centralizer z)) ∧
      (U ⊓ core z) ⊓ P=center (centralizer z) := by
  let := h.extraspecial
  obtain ⟨b,hb⟩ := original_point_marking h e X
  let P := pointCore h e X (b • p)
  refine ⟨P,pointCore_le h e X _,pointCore_elementary h e X _,pointCore_card h e X _,
    center_le_pointCore h e X _,pointCore_normalizes h e X _ J ?_,?_⟩
  · intro j hj
    rw [hb]
    change (b * designAutEquiv.symm (CubicLift.projection e j) * b⁻¹) • (b • p)=b • p
    rw [mul_smul,mul_smul,inv_smul_smul,hJ j hj]
  · apply le_antisymm
    · intro x hx
      obtain ⟨q,hq,rfl⟩ := hx.2
      have hqU : q.val ∈ U := hx.1.1
      have hz : (corePointProjection h e X q).toAdd=0 := by
        apply original_point_fixed_eq_zero h e X U hB hU p hp b hb _ hq
        intro u hu
        change M22TripleCover.Ambient.binaryAction
          (coreAmbientHom h e X (QuotientGroup.mk' (core z) u))
          (coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)))=_
        rw [←coreAmbientHom_intertwines]
        have he : MulAut.conjNormal u q=q := by
          apply Subtype.ext
          change u*q.val*u⁻¹=q.val
          have hc := congrArg Subtype.val (Commute.all (⟨u,hu⟩ : U) ⟨q.val,hqU⟩).eq
          change u*q.val=q.val*u at hc
          rw [hc,mul_inv_cancel_right]
        rw [coreBinaryRepresentation_apply]
        change coreNativeEquiv h e X (Additive.ofMul
          (coreQuotientAction h (QuotientGroup.mk' (core z) u)
            (QuotientGroup.mk' (center (core z)) q))) = _
        rw [coreQuotientAction_mk,he]
        rfl
      have hqz : q ∈ center (core z) := by
        rw [←corePointProjection_ker h e X]
        exact Multiplicative.toAdd.injective hz
      rw [←core_center_eq_centralizer_center h]
      exact mem_map_of_mem _ hqz
    · exact le_inf (le_inf hZU (core_center_eq_centralizer_center h ▸ map_subtype_le _))
        (center_le_pointCore h e X _)
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
