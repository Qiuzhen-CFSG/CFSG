module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.Marks
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import Theory.Representation.BinaryPairedTransvections.Fixed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Three-dimensional coordinates for the actual marked partner

A nonzero vector in a binary three-space can be sent to the first standard
basis vector. In these coordinates the full center-transvection group is
the literal marked point radical in SL₃(2): its natural action gives an
injective homomorphism between the two groups of order four. The inverse
dual coordinates retain the simultaneous contragredient action.

The final adapter constructs `Partner.MarkedAction` from the original paired
coordinates and surjective parameter, retaining the exact E, Eᵗ and V₀
quotient images. The source polar-geometry producer supplies those inputs;
no identification with the separate recognized K-module coordinates is used.

Source: Aschbacher–Smith, 15.3.56(4–5) and 15.3.58(2), printed pp.1148–1149.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MarkedCoordinates
open BinaryPairedTransvections BinaryTransvectionGroups BinaryLinear
open Core.ResidualGeneration
open Matrix.PSL3Two.MarkedAutomorphisms
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private theorem marked_coordinates [FiniteDimensional (ZMod 2) E]
    (hdim : Module.finrank (ZMod 2) E=3) (c : E) (hc : c ≠ 0) :
    ∃ e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector, e c=Partner.centerVector := by
  have hdim' : Module.finrank (ZMod 2) E=Module.finrank (ZMod 2) BinaryLinearThree.Vector := by
    simpa using hdim
  let e := LinearEquiv.ofFinrankEq E BinaryLinearThree.Vector hdim'
  have hec : e c ≠ 0 := fun h => hc (e.map_eq_zero_iff.mp h)
  have hpoint : (Partner.centerVector:BinaryLinearThree.Vector) ≠ 0 := by
    intro h
    have hh := congrFun h 0
    exact one_ne_zero hh
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) BinaryLinearThree.Vector (e c) hec
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) BinaryLinearThree.Vector Partner.centerVector hpoint
  obtain ⟨a,ha⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e.trans a,?_⟩
  have hh := ha (ex 1)
  simp only [LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] at hh
  simpa [ex,ey] using hh.symm

private def pointForm (a : pointV) : Module.Dual (ZMod 2) BinaryLinearThree.Vector :=
  a.val.val 0 1 • LinearMap.proj 1 + a.val.val 0 2 • LinearMap.proj 2

private theorem pointForm_center (a : pointV) : pointForm a Partner.centerVector=0 := by
  simp [pointForm,Partner.centerVector]

private theorem point_action (a : pointV) (v : BinaryLinearThree.Vector) :
    Matrix.SpecialLinearGroup.toLin' a.val v=v+pointForm a v • Partner.centerVector := by
  obtain ⟨h00,h10,h20,h11,h12,h21,h22⟩ := a.property
  change a.val.val.mulVec v=v+pointForm a v • Partner.centerVector
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_three,pointForm,Partner.centerVector,
    h00,h10,h20,h11,h12,h21,h22,add_assoc]

private def pointToCenter (c : E) (e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : e c=Partner.centerVector) (hc : c ≠ 0) : pointV →* centerGroup c where
  toFun a := ⟨e.trans ((Matrix.SpecialLinearGroup.toLin' a.val).trans e.symm),by
    apply (mem_centerGroup_iff c hc _).mpr
    let f := (pointForm a).comp e.toLinearMap
    have hf : f c=0 := by change pointForm a (e c)=0; rw [he,pointForm_center]
    refine ⟨f,hf,?_⟩
    ext v
    change e.symm (Matrix.SpecialLinearGroup.toLin' a.val (e v))=v+f v • c
    rw [point_action,map_add,map_smul,e.symm_apply_apply,←he,e.symm_apply_apply]
    rfl⟩
  map_one' := by
    apply Subtype.ext
    ext v
    change e.symm (Matrix.SpecialLinearGroup.toLin' 1 (e v))=v
    rw [map_one]
    exact e.symm_apply_apply v
  map_mul' a b := by
    apply Subtype.ext
    ext v
    change e.symm (Matrix.SpecialLinearGroup.toLin' (a.val*b.val) (e v))=
      e.symm (Matrix.SpecialLinearGroup.toLin' a.val
        (e (e.symm (Matrix.SpecialLinearGroup.toLin' b.val (e v)))))
    rw [e.apply_symm_apply,map_mul]
    rfl

private theorem pointToCenter_injective (c : E) (e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : e c=Partner.centerVector) (hc : c ≠ 0) : Function.Injective (pointToCenter c e he hc) := by
  intro a b hab
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  have hh := congrArg (fun a : centerGroup c => a.val (e.symm v)) hab
  change e.symm (Matrix.SpecialLinearGroup.toLin' a.val (e (e.symm v)))=
    e.symm (Matrix.SpecialLinearGroup.toLin' b.val (e (e.symm v))) at hh
  simpa only [e.apply_symm_apply,e.symm.injective.eq_iff] using hh

private def pointEquiv [FiniteDimensional (ZMod 2) E]
    (hdim : Module.finrank (ZMod 2) E=3) (c : E) (e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : e c=Partner.centerVector) (hc : c ≠ 0) : pointV ≃* centerGroup c := by
  classical
  let : Finite E := Module.finite_of_finite (ZMod 2)
  apply MulEquiv.ofBijective (pointToCenter c e he hc)
  apply (pointToCenter_injective c e he hc).bijective_of_nat_card_le
  rw [centerGroup_card c hc 1 (by simpa using hdim),card_pointV]
  decide

private theorem pointEquiv_action [FiniteDimensional (ZMod 2) E]
    (hdim : Module.finrank (ZMod 2) E=3) (c : E) (e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : e c=Partner.centerVector) (hc : c ≠ 0) (a : centerGroup c) (v : E) :
    e (a.val v)=BinaryLinearThree.W ((pointEquiv hdim c e he hc).symm a).val (e v) := by
  have hh := congrArg (fun a : centerGroup c => e (a.val v))
    ((pointEquiv hdim c e he hc).apply_symm_apply a)
  change e (e.symm (Matrix.SpecialLinearGroup.toLin'
    ((pointEquiv hdim c e he hc).symm a).val (e v)))=e (a.val v) at hh
  change e (a.val v)=Matrix.SpecialLinearGroup.toLin' _ (e v)
  simpa only [e.apply_symm_apply] using hh.symm


private theorem pointEquiv_dual_action [FiniteDimensional (ZMod 2) E]
    (hdim : Module.finrank (ZMod 2) E=3) (c : E) (e : E ≃ₗ[ZMod 2] BinaryLinearThree.Vector)
    (he : e c=Partner.centerVector) (hc : c ≠ 0) (a : centerGroup c)
    (f : Module.Dual (ZMod 2) E) :
    e.symm.dualMap (contragredient a.val f)=
      BinaryLinearThree.W.dual ((pointEquiv hdim c e he hc).symm a).val (e.symm.dualMap f) := by
  apply LinearMap.ext
  intro v
  change f (a.val.symm (e.symm v))=
    f (e.symm (BinaryLinearThree.W (((pointEquiv hdim c e he hc).symm a).val)⁻¹ v))
  apply congrArg f
  apply e.injective
  rw [e.apply_symm_apply]
  have hh := pointEquiv_action hdim c e he hc a⁻¹ (e.symm v)
  rw [map_inv] at hh
  simpa only [Subgroup.coe_inv,e.apply_symm_apply,LinearEquiv.coe_inv] using hh

variable {G : Type*} [Group G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]

/-- The three-dimensional paired action constructs the literal marked source
coordinates, including its full point-radical parameter and dual action. -/
theorem markedAction_of_paired [FiniteDimensional (ZMod 2) E]
    (V₀ : Subgroup G) (y t : G) (hXH : partnerX Z ZS y ≤ centralizerH Z)
    (hdim : Module.finrank (ZMod 2) E=3) (c : E) (hc : c ≠ 0)
    (b : Recognition.Space Z ZS ≃ₗ[ZMod 2] PairedSpace E)
    (hE : ∀ w : VectorQuotient Z ZS,
      w∈Partner.vectorImage Z ZS (intersectionE Z ZS y) ↔ (b (Additive.ofMul w)).2=0)
    (hEt : ∀ w : VectorQuotient Z ZS,
      w∈Partner.vectorImage Z ZS (rightConjugate (intersectionE Z ZS y) t) ↔
        (b (Additive.ofMul w)).1=0)
    (hcenter : ∀ w : VectorQuotient Z ZS,
      w∈Partner.vectorImage Z ZS V₀ ↔ ∃ a : ZMod 2,b (Additive.ofMul w)=(a • c,0))
    (p : partnerX Z ZS y →* centerGroup c) (hp : Function.Surjective p)
    (haction : ∀ (x : partnerX Z ZS y) (w : VectorQuotient Z ZS),
      b (Additive.ofMul (quotientAction Z ZS ⟨x,hXH x.property⟩ w))=
        pairedAction (p x).val (b (Additive.ofMul w))) :
    Nonempty (Partner.MarkedAction Z ZS V₀ y t hXH) := by
  obtain ⟨e,he⟩ := marked_coordinates hdim c hc
  let q := pointEquiv hdim c e he hc
  let l := b.trans (e.prodCongr e.symm.dualMap)
  let coordinates : VectorQuotient Z ZS ≃* Multiplicative NaturalDualSpace :=
    l.toAddEquiv.toMultiplicativeRight
  let parameter : partnerX Z ZS y →* pointV := q.symm.toMonoidHom.comp p
  refine ⟨{
    coordinates := coordinates
    E_image := ?_
    Et_image := ?_
    center_image := ?_
    parameter := parameter
    full := q.symm.surjective.comp hp
    equivariant := ?_ }⟩
  · intro w
    change w∈Partner.vectorImage Z ZS (intersectionE Z ZS y) ↔
      e.symm.dualMap (b (Additive.ofMul w)).2=0
    rw [hE]
    exact e.symm.dualMap.map_eq_zero_iff.symm
  · intro w
    change w∈Partner.vectorImage Z ZS (rightConjugate (intersectionE Z ZS y) t) ↔
      e (b (Additive.ofMul w)).1=0
    rw [hEt]
    exact e.map_eq_zero_iff.symm
  · intro w
    change w∈Partner.vectorImage Z ZS V₀ ↔
      ∃ a : ZMod 2,(e.prodCongr e.symm.dualMap) (b (Additive.ofMul w))=
        (a • Partner.centerVector,0)
    rw [hcenter]
    constructor
    · rintro ⟨a,ha⟩
      refine ⟨a,?_⟩
      rw [ha]
      change (e (a • c),e.symm.dualMap 0)=(a • Partner.centerVector,0)
      rw [map_smul,he,map_zero]
    · rintro ⟨a,ha⟩
      refine ⟨a,?_⟩
      apply (e.prodCongr e.symm.dualMap).injective
      rw [ha]
      change (a • Partner.centerVector,0)=(e (a • c),e.symm.dualMap 0)
      rw [map_smul,he,map_zero]
  · intro x w
    change (e.prodCongr e.symm.dualMap)
      (b (Additive.ofMul (quotientAction Z ZS ⟨x,hXH x.property⟩ w)))=
        (BinaryLinearThree.W (parameter x).val (e (b (Additive.ofMul w)).1),
          BinaryLinearThree.W.dual (parameter x).val
            (e.symm.dualMap (b (Additive.ofMul w)).2))
    rw [haction]
    apply Prod.ext
    · exact pointEquiv_action hdim c e he hc (p x) _
    · exact pointEquiv_dual_action hdim c e he hc (p x) _

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MarkedCoordinates
