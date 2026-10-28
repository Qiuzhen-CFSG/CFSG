module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint.Native
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeStabilizers
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient

/-!
# Elementary point preimages in the original extraspecial core

Pull a native singular point space back along the literal central quotient
of Q and the established James-module marking. Its full preimage is an
elementary subgroup of order 128 containing Z(Q), and conjugation in the
original centralizer carries it according to the full native point action.

The induced automorphism of Aut(M22) is inner. Consequently one design
conjugator aligns this point action with the original cubic projection,
uniformly for all centralizer elements. A subgroup fixing a point in the
original marking therefore preserves an actual elementary preimage.

This is the invariant-preimage step toward Aschbacher--Segev (4.8),
Invent. Math. 105 (1991), p.599, DOI 10.1007/BF01232280. The transversality
with the original cocode intersection must still be established separately.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
open Subgroup LocalGeometry Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22ValueBound.Concrete
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z) (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
  (X : Sylow 3 (CubicLift.subgroup e)) [IsExtraspecial 2 (core z)]

/-- The literal core projection in the established native quadratic coordinates. -/
def corePointProjection : core z →* Multiplicative BinarySpace :=
  (coreNativeEquiv h e X).toAddEquiv.toMultiplicative.toMonoidHom.comp
    (ExtraspecialSquare.projection (core z))

theorem corePointProjection_surjective : Function.Surjective (corePointProjection h e X) :=
  (coreNativeEquiv h e X).toAddEquiv.toMultiplicative.surjective.comp
    (ExtraspecialSquare.projection_surjective (core z))

theorem corePointProjection_ker : (corePointProjection h e X).ker = center (core z) := by
  rw [corePointProjection,MonoidHom.ker_comp_of_injective _
    (coreNativeEquiv h e X).toAddEquiv.toMultiplicative.toMonoidHom
    (coreNativeEquiv h e X).toAddEquiv.toMultiplicative.injective,
    ExtraspecialSquare.projection_ker]

/-- The full inverse image of a native point space, inside the original Q. -/
def pointPreimage (p : Fin 22) : Subgroup (core z) :=
  (pointSpace p).toAddSubgroup.toSubgroup.comap (corePointProjection h e X)

/-- The same subgroup viewed inside the original involution centralizer. -/
def pointCore (p : Fin 22) : Subgroup (centralizer z) :=
  (pointPreimage h e X p).map (core z).subtype

theorem pointCore_le (p : Fin 22) : pointCore h e X p ≤ core z := map_subtype_le _

theorem center_le_pointPreimage (p : Fin 22) : center (core z) ≤ pointPreimage h e X p := by
  intro x hx
  change (corePointProjection h e X x).toAdd ∈ pointSpace p
  have hk : x ∈ (corePointProjection h e X).ker := by rwa [corePointProjection_ker]
  rw [show corePointProjection h e X x = 1 from hk]
  exact (pointSpace p).zero_mem

theorem center_le_pointCore (p : Fin 22) : center (centralizer z) ≤ pointCore h e X p := by
  rw [←core_center_eq_centralizer_center h]
  exact map_mono (center_le_pointPreimage h e X p)

theorem pointPreimage_elementary (p : Fin 22) : IsElementaryAbelian 2 (pointPreimage h e X p) := by
  have hs (x : pointPreimage h e X p) : x^2=1 := by
    apply Subtype.ext
    apply (coreQuadraticForm_mk_eq_zero x.val).mp
    rw [← coreNativeEquiv_quadratic h e X]
    exact pointSpace_singular p _ x.property
  have hi (x : pointPreimage h e X p) : x⁻¹=x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs x)
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  intro a b
  rw [←hi (a*b),mul_inv_rev,hi,hi]

theorem pointCore_elementary (p : Fin 22) : IsElementaryAbelian 2 (pointCore h e X p) := by
  let := pointPreimage_elementary h e X p
  exact IsElementaryAbelian.map_subtype

theorem pointCore_card (p : Fin 22) : Nat.card (pointCore h e X p)=128 := by
  let f := corePointProjection h e X
  let U := (pointSpace p).toAddSubgroup.toSubgroup
  have hm : (pointPreimage h e X p).map f = U :=
    map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (corePointProjection_surjective h e X)]; exact le_top)
  have hc : Nat.card U=64 := by
    have eqv : U ≃ pointSpace p := {
      toFun x := ⟨x.val.toAdd,x.property⟩
      invFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    rw [Nat.card_congr eqv,Module.natCard_eq_pow_finrank (K := ZMod 2),
      pointSpace_finrank,Nat.card_zmod]
    norm_num
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (pointPreimage h e X p) f
  rw [corePointProjection_ker,inf_eq_right.mpr (center_le_pointPreimage h e X p),
    IsExtraspecial.center_order_p 2 (core z),hm,hc] at hh
  rw [pointCore,card_map_of_injective (core z).subtype_injective,←hh]

/-- Native point fixation gives literal conjugation invariance of its original preimage. -/
theorem pointCore_normalizes (p : Fin 22) (J : Subgroup (centralizer z))
    (hJ : ∀ j ∈ J, pointAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) j)) p=p) :
    J ≤ normalizer (pointCore h e X p : Set (centralizer z)) := by
  have stable (j : centralizer z) (hj : j ∈ J) (u : centralizer z)
      (hu : u ∈ pointCore h e X p) : j*u*j⁻¹ ∈ pointCore h e X p := by
    obtain ⟨u,hu,rfl⟩ := hu
    refine ⟨MulAut.conjNormal j u,?_,rfl⟩
    change coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z))
      (MulAut.conjNormal j u))) ∈ pointSpace p
    rw [←coreQuotientAction_mk h j u]
    change coreNativeEquiv h e X (coreBinaryRepresentation h (QuotientGroup.mk' (core z) j)
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) u))) ∈ pointSpace p
    rw [coreAmbientHom_intertwines]
    have hh := pointSpace_transport (coreAmbientHom h e X (QuotientGroup.mk' (core z) j))
      p (coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) u))) hu
    rwa [hJ j hj] at hh
  intro j hj
  apply mem_normalizer_iff.mpr
  intro u
  constructor
  · exact stable j hj u
  · intro hu
    have hh := stable j⁻¹ (J.inv_mem hj) _ hu
    simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel,inv_mul_cancel,mul_one] using hh

/-- The original automorphism marking and the native point action differ by
one design conjugator, uniformly for every original centralizer element. -/
theorem original_point_marking :
    ∃ b : m22DesignAut, ∀ j : centralizer z,
      pointAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) j)) =
        b.val * (designAutEquiv.symm (CubicLift.projection e j)).val * b.val⁻¹ := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  obtain ⟨a,ha⟩ := MulAut.automorphismTower_inner_of_isSimpleGroup m22_center_eq_bot
    (coreAmbientAutEquiv h e X)
  obtain ⟨b,hb⟩ := m22DesignAutToAut_surjective a
  refine ⟨b,?_⟩
  intro j
  have hh := coreAmbientAutEquiv_projection h e X (QuotientGroup.mk' (core z) j)
  have he : (⟨pointAction (coreAmbientHom h e X (QuotientGroup.mk' (core z) j)),
      pointAction_mem_design _⟩ : m22DesignAut) =
      b * designAutEquiv.symm (CubicLift.projection e j) * b⁻¹ := by
    apply m22DesignAutToAut_injective
    rw [pointAction_projection,map_mul,map_mul,map_inv]
    rw [←hh,←ha]
    change a * CubicLift.projection e j * a⁻¹ = _
    rw [hb]
    change a * CubicLift.projection e j * a⁻¹ =
      a * designAutEquiv (designAutEquiv.symm (CubicLift.projection e j)) * a⁻¹
    rw [MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val he

include h X in
/-- A subgroup fixing a point in the original Mathieu marking preserves an
actual elementary order-128 subgroup of Q containing its central marker. -/
theorem exists_original_pointCore (J : Subgroup (centralizer z)) (p : Fin 22)
    (hJ : ∀ j ∈ J, (designAutEquiv.symm (CubicLift.projection e j)) • p=p) :
    ∃ P : Subgroup (centralizer z), P ≤ core z ∧ IsElementaryAbelian 2 P ∧
      Nat.card P=128 ∧ center (centralizer z) ≤ P ∧ J ≤ normalizer (P : Set (centralizer z)) := by
  obtain ⟨b,hb⟩ := original_point_marking h e X
  refine ⟨pointCore h e X (b • p),pointCore_le h e X _,pointCore_elementary h e X _,
    pointCore_card h e X _,center_le_pointCore h e X _,pointCore_normalizes h e X _ J ?_⟩
  intro j hj
  rw [hb]
  change (b * designAutEquiv.symm (CubicLift.projection e j) * b⁻¹) • (b • p)=b • p
  rw [mul_smul,mul_smul,inv_smul_smul,hJ j hj]
end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.InvariantPoint
end
