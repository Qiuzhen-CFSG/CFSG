module
public import Theory.SpecificGroups.PSL3Four.CentralCover.CoreCommutatorQuotient
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSection
public import Theory.Representation.HermitianTensorThree.PlaneSection.Natural
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Theory.SpecificGroups.PSL3.ExceptionalFourCover.Basic
import all Theory.Representation.HermitianTensorThree.PlaneSection.Natural

/-!
# The marked four-space normalizer in native projective coordinates

The field transport sends the native line parabolic to exactly the binary
Hermitian transformations preserving the selected corner. Diagonal Hermitian
matrices force the lower-left matrix entries to vanish; the converse follows
by multiplication. Transporting this equivalence through the actual module
coordinates identifies N_L(U) with the full parabolic preimage.

The internal natural-section import reuses its lower-entry calculation.
Source: Aschbacher–Smith H.4.6(2) and 8.2.10(3), printed pp.382 and 721,
refs/quasithin.pdf. The Chapter 12 application keeps the original selected U.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
set_option backward.isDefEq.respectTransparency false

/-- Native field-four projective coordinates for the actual Hermitian image. -/
@[expose] def nativeBinaryEquiv : Matrix.PSL3Four.PSL ≃* binaryImage 1 :=
  (Matrix.PSL3.ExceptionalFourCover.baseEquiv (E 1) (by rw [card_E]; norm_num)).trans
    ((imageEquivPSL 1 (by decide)).symm.trans (binaryImageEquiv 1))

/-- The native quotient representative acts by the transported matrix. -/
theorem nativeBinaryEquiv_mk (a : SL(3,Matrix.PSL3Four.F)) :
    (nativeBinaryEquiv (QuotientGroup.mk' _ a)).val =
      binaryActionHom 1 (Atlas.fieldEquivSL 3
        (Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num)) a) := by
  change (binaryImageEquiv 1 ((imageEquivPSL 1 (by decide)).symm
    (Atlas.fieldEquivPSL 3
      (Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num))
        (QuotientGroup.mk' _ a)))).val = _
  rw [Atlas.fieldEquivPSL_mk]
  rw [←binaryImageEquiv_toImage]
  apply congrArg (fun x : Image 1 => (binaryImageEquiv 1 x).val)
  apply (imageEquivPSL 1 (by decide)).injective
  rw [MulEquiv.apply_symm_apply]
  exact (imageEquivPSL_toImage 1 (by decide) _).symm

private theorem corner_preserved_iff (a : Cover 1) :
    (∀ X ∈ PlaneSection.Corner, binaryActionHom 1 a X ∈ PlaneSection.Corner) ↔
      a 2 0=0 ∧ a 2 1=0 := by
  constructor
  · exact PlaneSection.lower_zero a
  · rintro ⟨h20,h21⟩ X hX
    obtain ⟨h22,h12,h02⟩ := (UnipotentRadicals.mem_plane_fixed_iff 1 X).mp hX
    apply (UnipotentRadicals.mem_plane_fixed_iff 1 _).mpr
    change (a.val * X.val * adjoint 1 a.val) 2 2=0 ∧
      (a.val * X.val * adjoint 1 a.val) 1 2=0 ∧
      (a.val * X.val * adjoint 1 a.val) 0 2=0
    simp [Matrix.mul_apply,Fin.sum_univ_three,adjoint,h20,h21,h22,h12,h02]

/-- The line parabolic is exactly the stabilizer of the Hermitian corner. -/
theorem native_line_parabolic_iff (a : Matrix.PSL3Four.PSL) :
    a ∈ Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F false ↔
      ∀ X ∈ PlaneSection.Corner, (nativeBinaryEquiv a).val X ∈ PlaneSection.Corner := by
  induction a using QuotientGroup.induction_on with
  | H a =>
    rw [show (QuotientGroup.mk a : Matrix.PSL3Four.PSL) = QuotientGroup.mk' _ a from rfl,
      nativeBinaryEquiv_mk,corner_preserved_iff]
    change a ∈ (Matrix.PSL3.LinearThree.lineParabolic Matrix.PSL3Four.F).comap
      (Matrix.PSL3.projection Matrix.PSL3Four.F) ↔ _
    rw [Matrix.PSL3.LinearThree.lineParabolic_comap,Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff]
    let k := Matrix.PSL3.ExceptionalFourCover.fieldEquiv (E 1) (by rw [card_E]; norm_num)
    change (a 2 0=0 ∧ a 2 1=0) ↔ (k (a 2 0)=0 ∧ k (a 2 1)=0)
    constructor
    · intro hh
      exact ⟨(congrArg k hh.1).trans (map_zero k), (congrArg k hh.2).trans (map_zero k)⟩
    · intro hh
      exact ⟨k.injective (hh.1.trans (map_zero k).symm),
        k.injective (hh.2.trans (map_zero k).symm)⟩

variable {G : Type*} [Group G] [Finite G]
open ChapterE
/-- The full original normalizer is the marked parabolic preimage. -/
theorem marked_corner_normalizer_preimage
    (V L U : Subgroup G) [IsElementaryAbelian 2 V]
    (hUV : U ≤ V) (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] Space 1) (q : L →* binaryImage 1)
    (he : ∀ (l : L) v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) = (q l).val (e v))
    (hU : ∀ v : Additive V, (v.toMul : G) ∈ U ↔ e v ∈ PlaneSection.Corner) :
    Matrix.PSL3Four.ElementaryParabolic.liftedParabolic
      (nativeBinaryEquiv.symm.toMonoidHom.comp q) false =
        (normalizer (U : Set G)).subgroupOf L := by
  ext l
  change nativeBinaryEquiv.symm (q l) ∈
    Matrix.PSL3.RootPlaneGeometry.parabolic Matrix.PSL3Four.F false ↔
      (l : G) ∈ normalizer (U : Set G)
  rw [native_line_parabolic_iff,nativeBinaryEquiv.apply_symm_apply]
  constructor
  · intro hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨u,hu,rfl⟩
      let v : Additive V := Additive.ofMul ⟨u,hUV hu⟩
      have hh := hp (e v) ((hU v).mp hu)
      rw [←he] at hh
      exact (hU _).mpr hh
    · exact (Nat.card_congr (U.equivMapOfInjective
        (MulAut.conj (l : G)).toMonoidHom (MulAut.conj (l : G)).injective).toEquiv).le
  · intro hn X hX
    obtain ⟨v,rfl⟩ := e.surjective X
    rw [←he]
    apply (hU _).mp
    exact (mem_normalizer_iff.mp hn _).mp ((hU v).mpr hX)
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
