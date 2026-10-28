module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.PointResidual
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.ResidualCover
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
-- Internal continuation: evaluate only the original quotient map on representatives.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original M22 cocode point C-component

The point homomorphism is factored through the original L/O₂(L), whose
map onto the simple M22 action image has central kernel. Restricting that
map gives the actual point residual a quasisimple two-core quotient, with
projective model PSL₃(4). In particular this keeps possible odd central
covering kernels in the original point subgroup.

Source: Aschbacher--Smith 8.1.1, printed p.712, refs/quasithin.pdf.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual point residual has the original quasisimple core quotient,
with its projective PSL₃(4) model; no covering center is discarded. -/
theorem sourceOrbit_m22_cocode_point_core_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    let R := solvableResidual (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)
    IsQuasisimple (R ⧸ pCore 2 R) ∧
      Nonempty (((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) ≃*
        Matrix.PSL3Four.PSL) := by
  let C := L ⊓ centralizer ({(x : G)} : Set G)
  let q := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion (show C ≤ L from inf_le_left))
  have hq : IsPGroup 2 q.ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let k : (L ⧸ pCore 2 L) →* M22 :=
    d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let c : Covering (L ⧸ pCore 2 L) M22 :=
    { toMonoidHom := k
      surjective := d.componentEquiv.surjective.comp
        (D.orbitComponentQuotientHom_surjective h) }
  obtain ⟨f,hf,hcomm,_,_⟩ := D.sourceOrbit_m22_cocode_point_residual d x i hx
  let j := (m22CocodeStabilizer m22CocodeRepresentation
    (m22WeightTwoVector i)).subtype.comp (m22WeightTwoVector_stabilizer_equiv i).symm.toMonoidHom
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (m22WeightTwoVector_stabilizer_equiv i).symm.injective
  obtain ⟨hqR,⟨e⟩⟩ := Chapter8.MathieuShadowRows.residual_central_quotient_of_factorization
    q hq k c.ker_le_center f hf j hj (fun a => (hcomm a).symm)
  refine ⟨hqR,⟨e.trans ?_⟩⟩
  have hz : center Matrix.PSL3Four.PSL = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 3) Matrix.PSL3Four.F)
  exact (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

/-- In the original local intersection, the embedded point residual is
normal and is a genuine C-component, with its full projective marking. -/
theorem sourceOrbit_m22_cocode_point_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCocodeRepresentation)
    (x : D.sourceOrbit) (i : Fin 22)
    (hx : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul x) = m22WeightTwoVector i) :
    let H := centralizer ({(x : G)} : Set G)
    let A := H ⊓ normalizer (L : Set G)
    let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    (B.subgroupOf A).Normal ∧ (B.subgroupOf A).IsCComponent ∧
      IsQuasisimple (B ⧸ pCore 2 B) ∧
      Nonempty (((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃*
        Matrix.PSL3Four.PSL) ∧ conjugateSpanBy B A = B := by
  let H := centralizer ({(x : G)} : Set G)
  let A := H ⊓ normalizer (L : Set G)
  let C := L ⊓ H
  let R := solvableResidual C
  let B := R.map C.subtype
  have hCA : C ≤ A := le_inf inf_le_right (inf_le_left.trans L.le_normalizer)
  have hn : A ≤ normalizer (C : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans H.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hBA : B ≤ A := (map_subtype_le _).trans hCA
  have hNB : A ≤ normalizer (B : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image C R)
  obtain ⟨hRq,⟨eR⟩⟩ := D.sourceOrbit_m22_cocode_point_core_quotient h d x i hx
  let : IsQuasisimple (R ⧸ pCore 2 R) := hRq
  have hp : IsPPerfect 2 R := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (R ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (R ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (R ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (R ⧸ N) inferInstance
  have hRc : R.IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : R.Normal).isSubnormal hp
  let eB : R ≃* B := R.equivMapOfInjective C.subtype C.subtype_injective
  let eQ : (B ⧸ pCore 2 B) ≃* (R ⧸ pCore 2 R) :=
    QuotientGroup.congr _ _ eB.symm (pCore_map_iso 2 eB.symm)
  have hcomp : (B.subgroupOf A).IsCComponent := by
    let eCA := (subgroupOfEquivOfLe hCA).symm
    have hh := (hRc.map_equiv eCA).map_subtype
      (normal_subgroupOf_of_le_normalizer hn).isSubnormal
    have he : (R.map eCA.toMonoidHom).map (C.subgroupOf A).subtype = B.subgroupOf A := by
      apply map_injective A.subtype_injective
      rw [map_subgroupOf_eq_of_le hBA,map_map,map_map]
      rfl
    exact he ▸ hh
  refine ⟨normal_subgroupOf_of_le_normalizer hNB,hcomp,
    IsQuasisimple.of_mulEquiv eQ.symm,⟨?_⟩,?_⟩
  · exact (QuotientGroup.congr _ _ eQ (FixedElementary.map_center eQ)).trans eR
  · exact le_antisymm (conjugateSpanBy_le le_rfl hNB) (le_conjugateSpanBy B A)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
