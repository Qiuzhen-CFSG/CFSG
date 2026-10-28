module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointClosure
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointClosure
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointCrossing
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock

/-!
# The original selected-plane crossing and dual irreducibility

The selected T-invariant four-space contains the original central involution.
Comparing its corner marking with the independent point marking puts V_z
in the original pair core. Its order 32 exceeds the four-space order 16,
so the original selected conjugator crosses the full closure E out of O₂(LT).

On this same tensor consumer the full kernel calculation identifies the
transvection kernel with V. The natural section then gives irreducibility
on O₂(L_z)/V by the separating commutator pairing. All new geometric and
kernel inputs are discharged, retaining the original Sylow, residual, action
and denominator. The initial closure conclusions are retained on the same z.

Source: Aschbacher–Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf. Exact local-core control, the remaining extraspecial
closure, 8.2.13 and the zero-weak-closure branch remain before full exclusion.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Stellmacher ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The same original selected pair crosses the actual point normal closure
out of the full LT core. Both independent Hermitian markings are compared. -/
theorem sourceOrbit_hermitian_selected_point_crossing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (z : D.sourceOrbit) (hne : z ≠ 1) (hzo : orderOf (z : G) = 2)
    (hZ : zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G)) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    (z : G) ∈ U ∧
      Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤ D.sourceOrbit ⊓ I.pCoreIn 2 ∧
      (¬ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤ U) ∧
      ¬ (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z).map
        (centralizer ({(z : G)} : Set G)).subtype ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  have hfix := D.sourceOrbit_omega_center_of_core_commutator h hmany hV hnon hcomm
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    (hfix.le.trans inf_le_right) (hZ.le (mem_zpowers _))
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,hrU,hUeq,_,hTU,_,_,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  have hUne : U ≠ ⊥ := by
    intro hh
    change rank U = 4 at hrU
    rw [hh,Representation.BinaryOffender.rank_bot] at hrU
    contradiction
  have hzU : (z : G) ∈ U := involution_mem_of_invariant_of_fixed_line
    (T : Subgroup G) U D.sourceOrbit z hzo T.isPGroup'
    ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left)
    hTU hUne inf_le_left (hfix.symm.trans hZ.symm)
  obtain ⟨c,hU,hB⟩ := selected_one_section_coordinates s D.sourceOrbit_weakClosure_setup
    (D.hermitianOrbitCoordinates 1 d) j hj he
  obtain ⟨a,ha⟩ := D.sourceOrbit_hermitian_point_marking d z hz hne
  let e := (D.hermitianOrbitCoordinates 1 d).trans a.val
  let q := (MulAut.conj a).toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  have hq : Function.Surjective q := (MulAut.conj a).surjective.comp
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
  have hk : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj a).injective,
      MonoidHom.ker_comp_of_injective _ _ d.groupEquiv.injective,
      D.hermitian_component_kernel h hmany hV hnon hcommL 1 d]
    exact pCore_isPGroup
  have heq (l : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) = (q l).val (e v) := by
    change a.val (D.hermitianOrbitCoordinates 1 d
      (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l) v)) =
        a.val ((d.groupEquiv (D.orbitComponentHom l)).val
          (a.val.symm (a.val (D.hermitianOrbitCoordinates 1 d v))))
    exact (congrArg a.val (D.hermitianOrbitCoordinates_component 1 d l v)).trans
      (congrArg (fun w => a.val ((d.groupEquiv (D.orbitComponentHom l)).val w))
        (a.val.symm_apply_apply (D.hermitianOrbitCoordinates 1 d v)).symm)
  have hW := marked_point_residual_coordinates D.sourceOrbit L
    D.sourceOrbit_component_normalizes e q heq hq hk z ha
  let b : binaryImage 1 := ⟨binaryActionHom 1 c,⟨c,rfl⟩⟩ * a⁻¹
  have hb (v : Additive D.sourceOrbit) :
      b.val (e v) = binaryActionHom 1 c (D.hermitianOrbitCoordinates 1 d v) := by
    change binaryActionHom 1 c (a.val.symm (a.val (D.hermitianOrbitCoordinates 1 d v))) = _
    rw [a.val.symm_apply_apply]
  have hbz : (b.val PointSection.pointVector).val 2 2 = 0 := by
    rw [←ha]
    change (b.val (e (Additive.ofMul z))).val 2 2 = 0
    rw [hb]
    exact ((UnipotentRadicals.mem_plane_fixed_iff 1 _).mp ((hU _).mp hzU)).1
  have hWB : Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤
      D.sourceOrbit ⊓ I.pCoreIn 2 := by
    intro w hw
    let v : Additive D.sourceOrbit := Additive.ofMul
      ⟨w,Chapter8.Section02.Centralizer.commutatorSpace_le L D.sourceOrbit z
        D.sourceOrbit_component_normalizes hw⟩
    apply (hB v).mpr
    change (binaryActionHom 1 c (D.hermitianOrbitCoordinates 1 d v)).val 2 2 = 0
    rw [←hb]
    exact PointSection.moved_image_hyperplane b hbz (e v) ((hW v).mp hw)
  have hUcard : Nat.card U = 16 := by
    obtain ⟨k,hk⟩ := ((IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le
      (show U ≤ D.sourceOrbit from inf_le_left)).exists_card_eq
    change rank U = 4 at hrU
    rw [rank,hk,Nat.log_pow Nat.one_lt_two] at hrU
    simpa [hrU] using hk
  have hWcard := D.sourceOrbit_hermitian_point_commutator_card h hmany hV hnon hcommL d z hz hne
  have hnot : ¬ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤ U := by
    intro hle
    have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [hUcard,hWcard] at hc
    omega
  exact ⟨hzU,hWB,hnot,selected_point_closure_crossing s D.sourceOrbit_weakClosure_setup
    L ((L ⊔ (T : Subgroup G)).pCoreIn 2) z D.sourceOrbit_component_normalizes
    (hV ▸ D.le_core) (hV ▸ D.core_centralizes) hUeq hzU hWB hnot⟩

/-- The literal tensor supplies the selected-plane crossing of 8.2.12
for the same central involution and the same original normal closure. -/
theorem sourceOrbit_hermitian_tensor_point_crossing
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
      ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
        zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
        Nat.card (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) = 32 ∧
        zpowers (z : G) < Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
        Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z < D.sourceOrbit ∧
        PointSectionActions D.sourceOrbit
          (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
          (Chapter8.Section02.Centralizer.localResidual L z) ∧
        FullPointTransvectionAction D.sourceOrbit (Chapter8.Section02.Centralizer.localTwoCore L z) z ∧
        Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z ≤
          pCore 2 (centralizer ({(z : G)} : Set G)) ∧
        ⁅Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z,
          pCore 2 (centralizer ({(z : G)} : Set G))⁆ ≤
          (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
        (∀ x : Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z,
          (x.val : G)^2 ∈ zpowers (z : G)) ∧
        (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
          (Chapter8.Section02.Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        IsElementaryAbelian 2 ((Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) ⧸
          center (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z)) ∧
        (∀ Y : Subgroup G, D.sourceOrbit ≤ Y →
          Y ≤ Chapter8.Section02.Centralizer.localTwoCore L z →
          Chapter8.Section02.Centralizer.localResidual L z ≤ normalizer (Y : Set G) →
          Y = D.sourceOrbit ∨ Y = Chapter8.Section02.Centralizer.localTwoCore L z) ∧
        ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
          Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
          let U := D.sourceOrbit ⊓ centralizer
            (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
          (z : G) ∈ U ∧
            Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤
              D.sourceOrbit ⊓ I.pCoreIn 2 ∧
            (¬ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ≤ U) ∧
            ¬ (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z).map
              (centralizer ({(z : G)} : Set G)).subtype ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,hWcard,hZW,hWV,hsections,htrans,hE,hEQ,hsq,hlocal,helem⟩ :=
    D.sourceOrbit_hermitian_tensor_point_closure
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨_,_,_,I,i,S,s,_,_,_,_,hTVA⟩ := D.sourceOrbit_hermitian_tensor_parabolic
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  obtain ⟨hcomm,hcommL⟩ := D.sourceOrbit_hermitian_selected_core_commutators
    h.toHypothesis1221 hV s hTVA
  have hker := D.sourceOrbit_hermitian_point_action_kernel h hmany hV hnon hcommL (z : G)
  have hker' := hker.trans (congrArg
    (fun U : Subgroup G => U.subgroupOf (Chapter8.Section02.Centralizer.localTwoCore L z))
    (hcore.symm.trans hV))
  have hzG : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
  have hdual := point_residual_dual_interval L D.sourceOrbit (z : G) hzG hZW.le
    hsections htrans hker'
  rcases hn with rfl
  exact ⟨rfl,hB,hw1,hcore,z,hzne,hzo,hZ,hWcard,hZW,hWV,hsections,htrans,
    hE,hEQ,hsq,hlocal,helem,hdual,H,I,i,S,s,D.sourceOrbit_hermitian_selected_point_crossing
      h hmany hV hnon hcomm hcommL d s z hzne hzo hZ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
