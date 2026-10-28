module
public import Theory.Representation.HermitianTensorThree.PointSection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCoverMarking
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy

/-!
# The actual point centralizer and its perfect residual

The native point parabolic is the stabilizer of the marked central vector
in the field-four Hermitian module. Equivariance identifies its full preimage
with the original C_L(z). Mapping the solvable residual and then removing its
intrinsic two-core gives SL₂(4), even when the covering map has a noncentral
two-group kernel. Relative normality in C_{N_G(L)}(z) makes this residual a
genuine C-component.

These are source 8.2.11(1) and the group quotient in (2), printed p.722,
refs/quasithin.pdf. The module sections in (2)–(4) remain separate calculations.
The Chapter 12 consumer constructs the point marking and the two-group kernel
on the original chosen module.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
set_option backward.isDefEq.respectTransparency false

/-- The native point parabolic is exactly the central-point stabilizer. -/
theorem native_point_parabolic_iff (a : Matrix.PSL3Four.PSL) :
    a ∈ Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true ↔
      (nativeBinaryEquiv a).val PointSection.pointVector = PointSection.pointVector := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [show (QuotientGroup.mk a : Matrix.PSL3Four.PSL) = QuotientGroup.mk' _ a from rfl,
      nativeBinaryEquiv_mk,PointSection.fixes_pointVector_iff]
    change a ∈ (Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F).comap
      (Matrix.PSL3.projection Matrix.PSL3Four.F) ↔ _
    rw [Matrix.PSL3.LinearThree.pointParabolic_comap,Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff]
    let k := Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num)
    change (a 1 0=0 ∧ a 2 0=0) ↔ (k (a 1 0)=0 ∧ k (a 2 0)=0)
    constructor
    · intro hh
      exact ⟨(congrArg k hh.1).trans (map_zero k), (congrArg k hh.2).trans (map_zero k)⟩
    · intro hh
      exact ⟨k.injective (hh.1.trans (map_zero k).symm),
        k.injective (hh.2.trans (map_zero k).symm)⟩

variable {G : Type*} [Group G] [Finite G]
open ChapterE
omit [Finite G] in
/-- The original involution centralizer is the full parabolic preimage. -/
theorem marked_point_centralizer_preimage
    (V L : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (z : V) (hz : e (Additive.ofMul z) = PointSection.pointVector) :
    Matrix.PSL3Four.ElementaryParabolic.liftedParabolic
      (nativeBinaryEquiv.symm.toMonoidHom.comp q) true =
        (centralizer ({(z : G)} : Set G)).subgroupOf L := by
  ext l
  change nativeBinaryEquiv.symm (q l) ∈
    Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F true ↔
      (l : G) ∈ centralizer ({(z : G)} : Set G)
  rw [native_point_parabolic_iff,nativeBinaryEquiv.apply_symm_apply,←hz,←he]
  rw [e.injective.eq_iff,mem_centralizer_singleton_iff]
  change (Additive.ofMul ⟨(l : G)*(z : G)*(l : G)⁻¹,_⟩ : Additive V) =
    Additive.ofMul z ↔ (l : G)*(z : G)=(z : G)*(l : G)
  rw [Additive.ofMul.injective.eq_iff,Subtype.ext_iff,mul_inv_eq_iff_eq_mul]

/-- Transport of the actual residual and its full two-core quotient. -/
theorem point_residual_quotient
    (L : Subgroup G) (z : G) (f : L →* Matrix.PSL3Four.PSL)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hP : Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true =
      (centralizer ({z} : Set G)).subgroupOf L) :
    Nonempty ((Centralizer.localResidual L z ⧸ pCore 2 (Centralizer.localResidual L z)) ≃*
      SL(2,Matrix.PSL3Four.F)) := by
  let P₀ := Matrix.PSL3Four.ElementaryParabolic.liftedParabolic f true
  let P := L ⊓ centralizer ({z} : Set G)
  have hPmap : P₀.map L.subtype = P := by
    dsimp only [P₀,P]
    rw [hP,subgroupOf_map_subtype,inf_comm]
  let eP : P₀ ≃* P := (P₀.equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr hPmap)
  have hRmap : (solvableResidual P₀).map (L.subtype.comp P₀.subtype) =
      Centralizer.localResidual L z := by
    have hm := congrArg (Subgroup.map P.subtype)
      (map_solvableResidual_eq eP.toMonoidHom eP.surjective)
    rw [map_map] at hm
    exact hm
  let eR := ((solvableResidual P₀).equivMapOfInjective (L.subtype.comp P₀.subtype)
    (L.subtype_injective.comp P₀.subtype_injective)).trans (MulEquiv.subgroupCongr hRmap)
  exact ⟨(eR.symm.toMonoidHom.pCoreQuotientEquiv eR.symm.surjective
    (IsPGroup.ker_isPGroup_of_injective eR.symm.injective)).trans
      (Matrix.PSL3Four.ElementaryParabolic.residualCoreQuotientEquiv f hf hk true)⟩

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (A ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (A ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ N) inferInstance

/-- Relative normality and the SL₂(4) quotient make the original perfect
residual a genuine C-component of C_{N_G(L)}(z). -/
theorem point_residual_component
    (L : Subgroup G) (z : G)
    (e : (Centralizer.localResidual L z ⧸ pCore 2 (Centralizer.localResidual L z)) ≃*
      SL(2,Matrix.PSL3Four.F)) :
    ((Centralizer.localResidual L z).subgroupOf
      (normalizer (L : Set G) ⊓ centralizer ({z} : Set G))).IsCComponent := by
  let R := Centralizer.localResidual L z
  let M := normalizer (L : Set G) ⊓ centralizer ({z} : Set G)
  have hRM : R ≤ M := (Centralizer.localResidual_le L z).trans
    (inf_le_inf_right _ L.le_normalizer)
  have hMN : M ≤ normalizer (R : Set G) := by
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
    exact (le_inf inf_le_left
      (inf_le_right.trans (centralizer ({z} : Set G)).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMN
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv
      (by rw [Matrix.PSL3Four.card_F]; decide) e
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) (pCore_isPGroup (p := 2)) (perfect_twoPerfect (A := R))
  have htop : (⊤ : Subgroup (R.subgroupOf M)).IsCComponent := by
    simpa using ht.map_equiv (subgroupOfEquivOfLe hRM).symm
  simpa only [←MonoidHom.range_eq_map,range_subtype] using
    htop.map_subtype (inferInstance : (R.subgroupOf M).Normal).isSubnormal

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
