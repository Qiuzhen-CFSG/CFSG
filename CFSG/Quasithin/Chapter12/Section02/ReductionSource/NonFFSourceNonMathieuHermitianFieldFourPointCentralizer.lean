module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCoreEquality
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCentralizer
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock

/-!
# The original central involution and its point-local residual

A Sylow subgroup of the actual component image marks the nonzero T-fixed
vector by an inner Hermitian actor. Its exact stabilizer preimage is C_L(z),
with kernel O₂(L). The source residual therefore has SL₂(4) as its quotient
by the full intrinsic two-core and is a genuine C-component of C_{N_G(L)}(z).

The tensor application constructs z from Ω₁Z(T), proves it generates that
order-two subgroup, and retains the preceding equality V = O₂(L). It has
no point-marking or residual-quotient premise. The internal imports reuse
the original conjugation formula and component-kernel proof.

Source: Aschbacher–Smith 8.2.11(1) and the group quotient in (2), printed
p.722, refs/quasithin.pdf. The module sections and 8.2.12–13, as well as
zero weak closure, remain necessary for the full Hermitian contradiction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Stellmacher ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original projection with the inner point marking retained. -/
@[expose] def hermitianPointProjection
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) (c : binaryImage 1) : L →* Matrix.PSL3Four.PSL :=
  nativeBinaryEquiv.symm.toMonoidHom.comp
    ((MulAut.conj c).toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom))

/-- Any original nontrivial T-fixed vector admits the literal inner point marking. -/
theorem sourceOrbit_hermitian_point_marking
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ c : binaryImage 1,
      c.val (D.hermitianOrbitCoordinates 1 d (Additive.ofMul z)) = PointSection.pointVector := by
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hST : (S : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hS]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let f := d.groupEquiv.toMonoidHom.comp D.orbitComponentHom
  let P := S.mapSurjective (f := f) (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
  let e := D.hermitianOrbitCoordinates 1 d
  apply PointSection.sylow_fixed_marking P (e (Additive.ofMul z))
  · intro a
    obtain ⟨l,hl,ha⟩ := a.property
    change overgroupAction 1 (binaryImage 1) (a : binaryImage 1) (e (Additive.ofMul z)) = _
    rw [←ha]
    change overgroupAction 1 (binaryImage 1) (d.groupEquiv (D.orbitComponentHom l))
      (e (Additive.ofMul z)) = _
    rw [←D.hermitianOrbitCoordinates_component 1 d l]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
    rw [hz l (hST (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
  · intro he
    apply hne
    exact congrArg Additive.toMul (e.injective (he.trans (map_zero e).symm))

omit [Finite G] in
private theorem pointProjection_preimage
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) (c : binaryImage 1)
    (z : D.sourceOrbit)
    (hc : c.val (D.hermitianOrbitCoordinates 1 d (Additive.ofMul z)) = PointSection.pointVector) :
    Matrix.PSL3Four.ElementaryParabolic.liftedParabolic (D.hermitianPointProjection d c) true =
      (centralizer ({(z : G)} : Set G)).subgroupOf L := by
  let e := (D.hermitianOrbitCoordinates 1 d).trans c.val
  let q := (MulAut.conj c).toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  have he (l : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) = (q l).val (e v) := by
    change c.val (D.hermitianOrbitCoordinates 1 d
      (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l) v)) =
        c.val ((d.groupEquiv (D.orbitComponentHom l)).val
          (c.val.symm (c.val (D.hermitianOrbitCoordinates 1 d v))))
    exact (congrArg c.val (D.hermitianOrbitCoordinates_component 1 d l v)).trans
      (congrArg (fun w => c.val ((d.groupEquiv (D.orbitComponentHom l)).val w))
        (c.val.symm_apply_apply (D.hermitianOrbitCoordinates 1 d v)).symm)
  exact marked_point_centralizer_preimage D.sourceOrbit L
    D.sourceOrbit_component_normalizes e q he z hc

/-- The original centralizer and residual are marked without losing any part
of their intrinsic two-cores. -/
theorem sourceOrbit_hermitian_point_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ c : binaryImage 1,
      c.val (D.hermitianOrbitCoordinates 1 d (Additive.ofMul z)) = PointSection.pointVector ∧
      Function.Surjective (D.hermitianPointProjection d c) ∧
      (D.hermitianPointProjection d c).ker = pCore 2 L ∧
      Matrix.PSL3Four.ElementaryParabolic.liftedParabolic (D.hermitianPointProjection d c) true =
        (centralizer ({(z : G)} : Set G)).subgroupOf L ∧
      Nonempty ((Chapter8.Section02.Centralizer.localResidual L z ⧸
        pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* SL(2,Matrix.PSL3Four.F)) ∧
      ((Chapter8.Section02.Centralizer.localResidual L z).subgroupOf
        (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent := by
  obtain ⟨c,hc⟩ := D.sourceOrbit_hermitian_point_marking d z hz hne
  let e := (D.hermitianOrbitCoordinates 1 d).trans c.val
  let q := (MulAut.conj c).toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  let f := D.hermitianPointProjection d c
  have hf : Function.Surjective f := nativeBinaryEquiv.symm.surjective.comp
    ((MulAut.conj c).surjective.comp (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective))
  have hk : f.ker = pCore 2 L := by
    change (nativeBinaryEquiv.symm.toMonoidHom.comp q).ker = pCore 2 L
    rw [MonoidHom.ker_comp_of_injective _ _ nativeBinaryEquiv.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective,
      MonoidHom.ker_comp_of_injective _ _ d.groupEquiv.injective]
    exact D.hermitian_component_kernel h hmany hV hnon hcommL 1 d
  have hP := D.pointProjection_preimage d c z hc
  have hpk : IsPGroup 2 f.ker := hk ▸ (pCore_isPGroup (p := 2))
  obtain ⟨ez⟩ := point_residual_quotient L (z : G) f hf hpk hP
  exact ⟨c,hc,hf,hk,hP,⟨ez⟩,point_residual_component L (z : G) ez⟩

private theorem generator_of_card_two (W Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hZW : Z ≤ W) (hc : Nat.card Z = 2) :
    ∃ z : W, z ≠ 1 ∧ orderOf (z : G) = 2 ∧ zpowers (z : G) = Z := by
  have hZne : Z ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by rw [hc]; decide)
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp hZne
  have hzn : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
  let zv : W := ⟨z,hZW z.property⟩
  have hvne : zv ≠ 1 := fun he => hzn (congrArg Subtype.val he)
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) (hZW z.property)) hzn
  refine ⟨zv,hvne,ho,?_⟩
  apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
  rw [Nat.card_zpowers,ho,hc]

private theorem point_centralizer_of_block
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (hz : omegaOneCenterAmbient (T : Subgroup G) = D.sourceOrbit ⊓ centralizer (T : Set G))
    (hzc : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) :
      ∃ (z : D.sourceOrbit), z ≠ 1 ∧ orderOf (z : G) = 2 ∧
        zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
          Nonempty ((Chapter8.Section02.Centralizer.localResidual L z ⧸
            pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* SL(2,Matrix.PSL3Four.F)) ∧
          ((Chapter8.Section02.Centralizer.localResidual L z).subgroupOf
            (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent := by
  obtain ⟨zv,hvne,ho,hZ⟩ := generator_of_card_two D.sourceOrbit
    (omegaOneCenterAmbient (T : Subgroup G)) (hz.le.trans inf_le_left) hzc
  have hzf : (zv : G) ∈ centralizer (T : Set G) :=
    (hz.le.trans inf_le_right) (hZ.le (mem_zpowers _))
  obtain ⟨c,hc,hf,hk,hP,he,hcomp⟩ := D.sourceOrbit_hermitian_point_centralizer
    h hmany hV hnon hcommL d zv hzf hvne
  exact ⟨zv,hvne,ho,hZ,he,hcomp⟩


/-- The positive-closure tensor supplies the central involution and source
8.2.11(1) with its SL₂(4) quotient. The preceding marked theorem retains the
exact parabolic preimage. -/
theorem sourceOrbit_hermitian_tensor_point_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : 0 < globalW D.sourceOrbit T) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧ V = L.pCoreIn 2 ∧
      ∃ (z : D.sourceOrbit), z ≠ 1 ∧ orderOf (z : G) = 2 ∧
        zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
          Nonempty ((Chapter8.Section02.Centralizer.localResidual L z ⧸
            pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* SL(2,Matrix.PSL3Four.F)) ∧
          ((Chapter8.Section02.Centralizer.localResidual L z).subgroupOf
            (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent := by
  have hc0 := D.sourceOrbit_hermitian_tensor_core_eq
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  have hb0 := D.sourceOrbit_hermitian_tensor_block_structure
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨hn,hB,hw1,hcore⟩ := hc0
  obtain ⟨_,_,_,_,hcommL,_,_,_,_,_,_,hz,hzc⟩ := hb0
  have hdegree1 : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = 1 := hdegree.trans hn
  have hfield1 : B.degree = 2*1 := hfield.trans (congrArg (fun k : ℕ => 2*k) hn)
  have hmodel1 : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) 1 := hn ▸ hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree1 hfield1 hmodel1
  exact ⟨hn,hB,hw1,hcore,D.point_centralizer_of_block
    h hmany hV hnon hcommL hz hzc d⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
