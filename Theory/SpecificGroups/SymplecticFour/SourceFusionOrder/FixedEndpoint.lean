module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.OuterConjugacy
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Binary.PointModel
public import Theory.SpecificGroups.SymplecticFour.Binary.PlaneModel
public import Theory.GroupTheory.PResidual.PGroupFactor
public import Theory.SpecificGroups.SymmetricFour.ResidualFactorization

/-!
# Compatible binary fixed parabolics of an outer symplectic involution

Borel descent conjugates the outer flag involution to Frobenius. Descending
its fixed matrices to the binary coefficient field preserves both coordinate
parabolics. Restriction of this single equivalence gives an isomorphism of
the fixed amalgam, including its whole fixed Borel. The binary endpoint
models C2 x S4 identify both actual two-residuals with A4.

This supplies the compatible fixed pair used in the exceptional Sp4(4)
argument of Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf.
The original ambient application is in Chapter6's SymplecticExtensionOrder
FixedEndpoint module; the subsequent V4/D8 quotient obstruction is separate.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open DiagramAutomorphisms FieldFixedResidual
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def conjugateFixedEquiv {J : Type*} [Group J] (e b : MulAut J) :
    b.fixedSubgroup ≃* (e*b*e⁻¹).fixedSubgroup where
  toFun x := ⟨e x.val, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    simp only [MulAut.mul_apply,MulAut.inv_apply,e.symm_apply_apply]
    rw [(MulAut.mem_fixedSubgroup _ _).mp x.property]⟩
  invFun y := ⟨e.symm y.val, by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply e.injective
    have hh := (MulAut.mem_fixedSubgroup _ _).mp y.property
    simpa only [MulAut.mul_apply,MulAut.inv_apply,e.apply_symm_apply] using hh⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul x.val y.val)

omit [Finite F] [CharP F 2] in
private theorem fixedEquiv_point (σ : F ≃+* F) (x : (fieldAutomorphism σ).fixedSubgroup) :
    fixedEquiv σ x ∈ pointParabolic ↔ x.val ∈ pointParabolic := by
  simp only [mem_pointParabolic_iff]
  change ((⟨_,_⟩ : fixedField σ)=0 ∧ ∀ i, (⟨_,_⟩ : fixedField σ)=0) ↔ _
  simp only [Subtype.ext_iff,ZeroMemClass.coe_zero]
  have hh := fixedEquiv_inclusion σ x
  have hc (i j : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val i j) hh
  simp only [coefficientInclusion_apply] at hc
  simp only [hc]

omit [Finite F] [CharP F 2] in
private theorem fixedEquiv_plane (σ : F ≃+* F) (x : (fieldAutomorphism σ).fixedSubgroup) :
    fixedEquiv σ x ∈ planeParabolic ↔ x.val ∈ planeParabolic := by
  simp only [mem_planeParabolic_iff]
  change (∀ i j, (⟨_,_⟩ : fixedField σ)=0) ↔ _
  simp only [Subtype.ext_iff,ZeroMemClass.coe_zero]
  have hh := fixedEquiv_inclusion σ x
  have hc (i j : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val i j) hh
  simp only [coefficientInclusion_apply] at hc
  simp only [hc]

/-- A single equivalence identifies the fixed native group with Sp4(2)
and preserves both marked parabolics, hence their whole intersection. -/
theorem outer_fixed_binary_flag (hF : Nat.card F=4)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    ∃ e : a.fixedSubgroup ≃* Sp (ZMod 2),
      (∀ x, e x ∈ pointParabolic ↔ x.val ∈ pointParabolic) ∧
      (∀ x, e x ∈ planeParabolic ↔ x.val ∈ planeParabolic) := by
  obtain ⟨c,hc⟩ := outer_flag_involution_frobenius hF a hao ha hi
  subst a
  let σ := frobeniusEquiv F 2
  let K := fixedField σ
  have hK : Nat.card K=2 := by
    simpa only [halfField,pow_one] using card_halfField (F := F)
      (m := 1) (by decide) (show Nat.card F=2^(2*1) from hF)
  let t := Binary.fieldEquivSp (Binary.fieldEquivZModTwo K hK)
  let b := conjugateFixedEquiv (MulAut.conj c.val) (fieldAutomorphism σ)
  let e := b.symm.trans ((fixedEquiv σ).trans t)
  refine ⟨e,?_,?_⟩
  · intro x
    change t (fixedEquiv σ (b.symm x)) ∈ pointParabolic ↔ _
    rw [Binary.fieldEquivSp_mem_pointParabolic,fixedEquiv_point]
    have hn := pointParabolic.le_normalizer c.property.1
    have hh : c.val*(b.symm x).val*c.val⁻¹=x.val :=
      congrArg Subtype.val (b.apply_symm_apply x)
    simpa only [hh,SetLike.mem_coe] using hn ((b.symm x).val)
  · intro x
    change t (fixedEquiv σ (b.symm x)) ∈ planeParabolic ↔ _
    rw [Binary.fieldEquivSp_mem_planeParabolic,fixedEquiv_plane]
    have hn := planeParabolic.le_normalizer c.property.2
    have hh : c.val*(b.symm x).val*c.val⁻¹=x.val :=
      congrArg Subtype.val (b.apply_symm_apply x)
    simpa only [hh,SetLike.mem_coe] using hn ((b.symm x).val)

/-- The fixed subamalgam retains the full fixed common Borel. -/
@[expose] def fixedDiagram (a : MulAut (Sp F)) :=
  Theory.GroupTheory.RankTwoAmalgam.ofSubgroups
    (pointParabolic ⊓ a.fixedSubgroup) (borel ⊓ a.fixedSubgroup)
    (planeParabolic ⊓ a.fixedSubgroup)
    (inf_le_inf inf_le_left le_rfl) (inf_le_inf inf_le_right le_rfl)

private def fixedRestriction {J : Type*} [Group J]
    (a : MulAut (Sp F)) (e : a.fixedSubgroup ≃* J)
    (P : Subgroup (Sp F)) (Q : Subgroup J)
    (he : ∀ x, e x ∈ Q ↔ x.val ∈ P) : (P ⊓ a.fixedSubgroup : Subgroup (Sp F)) ≃* Q where
  toFun x := ⟨e ⟨x.val,x.property.2⟩,(he _).mpr x.property.1⟩
  invFun y := ⟨(e.symm y.val).val,⟨(he _).mp (by rw [e.apply_symm_apply]; exact y.property),
    (e.symm y.val).property⟩⟩
  left_inv x := Subtype.ext (congrArg (fun z : a.fixedSubgroup => z.val)
    (e.symm_apply_apply ⟨x.val,x.property.2⟩))
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_mul' x y := Subtype.ext (e.map_mul ⟨x.val,x.property.2⟩ ⟨y.val,y.property.2⟩)

/-- The binary identification is compatible on both endpoints and on the
whole fixed Borel; it is an isomorphism of the literal fixed amalgam. -/
theorem outer_fixed_binary_amalgam (hF : Nat.card F=4)
    (a : MulAut (Sp F)) (hao : orderOf a=2)
    (ha : a ∈ SourceNormalizerExtension.flagAutomorphisms F)
    (hi : a ∉ MulAut.innerSubgroup (Sp F)) :
    Nonempty (Theory.GroupTheory.RankTwoAmalgam.Iso (fixedDiagram a)
      (SourceNormalizerExtension.diagram (ZMod 2))) := by
  obtain ⟨e,heP,heQ⟩ := outer_fixed_binary_flag hF a hao ha hi
  have heB (x : a.fixedSubgroup) : e x ∈ borel ↔ x.val ∈ borel :=
    and_congr (heP x) (heQ x)
  exact ⟨{
    left := fixedRestriction a e pointParabolic pointParabolic heP
    right := fixedRestriction a e planeParabolic planeParabolic heQ
    middle := fixedRestriction a e borel borel heB
    left_commutes _ := by apply Subtype.ext; rfl
    right_commutes _ := by apply Subtype.ext; rfl }⟩

private theorem symmetricTwo_isTwoGroup : IsPGroup 2 (Equiv.Perm (Fin 2)) := by
  apply IsPGroup.of_card (n := 1)
  norm_num [Nat.card_eq_fintype_card,Fintype.card_perm]

/-- The actual binary point parabolic has two-residual A4. -/
def binary_point_twoResidual_equiv :
    pResidual 2 (pointParabolic (F := ZMod 2)) ≃* alternatingGroup (Fin 4) :=
  (pResidualEquivOfPGroupFactor 2 Binary.pointParabolicZModEquivProd
    symmetricTwo_isTwoGroup).trans
      (MulEquiv.subgroupCongr Theory.SpecificGroups.SymmetricFourResidual.residual_eq)

/-- The actual binary plane parabolic has two-residual A4. -/
def binary_plane_twoResidual_equiv :
    pResidual 2 (planeParabolic (F := ZMod 2)) ≃* alternatingGroup (Fin 4) :=
  (pResidualEquivOfPGroupFactor 2 Binary.planeParabolicZModEquivProd
    symmetricTwo_isTwoGroup).trans
      (MulEquiv.subgroupCongr Theory.SpecificGroups.SymmetricFourResidual.residual_eq)

end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
