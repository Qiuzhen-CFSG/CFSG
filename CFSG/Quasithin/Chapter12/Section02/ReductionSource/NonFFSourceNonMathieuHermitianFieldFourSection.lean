module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPairNormalizer
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSection
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The original Hermitian section action and its full kernel

For every original parameter-one selection, the same cover conjugator
identifies B₀ = V ∩ O₂(I) with the canonical eight-space and U with its
Hermitian corner. The matrix calculation equates C_R(B₀/U) and C_R(U).
The established residual kernel therefore gives C_R(B₀/U)=O₂(R), with
R = N_L(U)^∞ and the original possibly nonfaithful component retained.

We also construct conjugation on the literal B₀/U and record its value on
every quotient representative. The half-field tensor application combines
this with the selected-pair normalizer, discharging the normalization and
section-kernel premises at the same original four-space and component.
This supplies the hB input in Normalizer.TensorRecognition.pairSection_kernel;
the P/U product action, full natural/tensor marking, equality R=K, zero weak
closure exclusion and the remaining 8.2.8–13 argument are still required.

Source: Aschbacher–Smith H.4.6(2) and 8.2.8(4), printed pp.382 and718,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The kernel on B/U for each original parameter-one selection is O₂(R).
The section and its conjugation representatives are the original ones. -/
theorem sourceOrbit_hermitian_selected_section_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ∀ r : R, (∀ b : ↥(D.sourceOrbit ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔
      r ∈ pCore 2 R := by
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  obtain ⟨c,hU,hB⟩ := selected_one_section_coordinates s D.sourceOrbit_weakClosure_setup
    (D.hermitianOrbitCoordinates 1 d) j hj he
  let z := binaryActionHom 1 c
  let z' : binaryImage 1 := ⟨z,⟨c,rfl⟩⟩
  let e := (D.hermitianOrbitCoordinates 1 d).trans z
  let q := (MulAut.conj z').toMonoidHom.comp
    (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  let l := (MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)
  have hl (a : Automizer D.sourceOrbit) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit a v) = l a (e v) := by
    change z (D.hermitianOrbitCoordinates 1 d (automizerRepresentation D.sourceOrbit a v)) =
      z ((j a).val (z.symm (z (D.hermitianOrbitCoordinates 1 d v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have heq (a : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes a)) v) = (q a).val (e v) := by
    change e (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer a) v) = _
    rw [hl]
    change z ((j (D.hermitianComponentAutomizer a)).val (z.symm (e v))) =
      z ((d.groupEquiv (D.orbitComponentHom a)).val (z.symm (e v)))
    exact congrArg (fun t : (Space 1 ≃ₗ[ZMod 2] Space 1) => z (t (z.symm (e v)))) (hcomp a)
  obtain ⟨hker,_⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h d s
  change ∀ r : R, (∀ b : ↥(D.sourceOrbit ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔ r ∈ pCore 2 R
  intro r
  have hr := Chapter8.Section02.Normalizer.localResidual_le L U r.property
  have hc := field_four_section_centralizer D.sourceOrbit L
    (D.sourceOrbit ⊓ I.pCoreIn 2) U inf_le_left inf_le_left
    D.sourceOrbit_component_normalizes e q heq hU hB ⟨r,hr.1⟩ hr.2
  change (∀ b : ↥(D.sourceOrbit ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔ _
  rw [hc]
  constructor
  · intro hrc
    have hm : (r : G) ∈ R.pCoreIn 2 := hker.le ⟨r.property,hrc⟩
    obtain ⟨a,ha,har⟩ := hm
    exact (show a = r from Subtype.ext har) ▸ ha
  · intro hrp
    exact (hker.ge (mem_map_of_mem R.subtype hrp)).2

/-- Canonical conjugation on the actual B/U, retaining quotient representatives
and the full two-core kernel. The preceding pair-normalizer theorem supplies hRP. -/
theorem sourceOrbit_hermitian_selected_section_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hRP : Chapter8.Section02.Normalizer.localResidual L (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) ≤
        normalizer (I.pCoreIn 2 : Set G)) :
    let B₀ := D.sourceOrbit ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    ∃ hRB : R ≤ normalizer (B₀ : Set G),
      ∃ hU : (U.subgroupOf B₀).Normal, letI := hU
        ∃ f : R →* MulAut (B₀ ⧸ U.subgroupOf B₀),
          f.ker = pCore 2 R ∧
          ∀ (r : R) (b : B₀), f r (QuotientGroup.mk' (U.subgroupOf B₀) b) =
            QuotientGroup.mk' (U.subgroupOf B₀)
              (B₀.normalizerMonoidHom (inclusion hRB r) b) := by
  let B₀ := D.sourceOrbit ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let : IsElementaryAbelian 2 B₀ := IsElementaryAbelian.of_le
    (show B₀ ≤ D.sourceOrbit from inf_le_left)
  have hU : (U.subgroupOf B₀).Normal := inferInstance
  let := hU
  have hRU : R ≤ normalizer (U : Set G) :=
    (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right
  have hRB : R ≤ normalizer (B₀ : Set G) :=
    (le_inf ((Chapter8.Section02.Normalizer.localResidual_le L U).trans
      (inf_le_left.trans D.sourceOrbit_component_normalizes)) hRP).trans
        inf_normalizer_le_normalizer_inf
  let a : R →* MulAut B₀ := B₀.normalizerMonoidHom.comp (inclusion hRB)
  have ha (r : R) : (U.subgroupOf B₀).map (a r).toMonoidHom = U.subgroupOf B₀ := by
    ext b
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact (mem_normalizer_iff.mp (hRU r.property) _).mp hv
    · intro hb
      refine ⟨(a r).symm b,?_,(a r).apply_symm_apply b⟩
      exact (mem_normalizer_iff.mp (hRU r.property) _).mpr
        (show (a r ((a r).symm b) : G) ∈ U by rw [(a r).apply_symm_apply]; exact hb)
  let f : R →* MulAut (B₀ ⧸ U.subgroupOf B₀) := {
    toFun := fun r => QuotientGroup.congr _ _ (a r) (ha r)
    map_one' := by
      ext b
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B₀) b
      change QuotientGroup.mk' _ (a 1 b) = QuotientGroup.mk' _ b
      rw [map_one]
      rfl
    map_mul' := fun r t => by
      ext b
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B₀) b
      change QuotientGroup.mk' _ (a (r*t) b) = QuotientGroup.mk' _ (a r (a t b))
      rw [map_mul]
      rfl }
  have hf (r : R) (b : B₀) :
      f r (QuotientGroup.mk' (U.subgroupOf B₀) b) =
        QuotientGroup.mk' (U.subgroupOf B₀) (a r b) := rfl
  refine ⟨hRB,hU,f,?_,fun _ _ => rfl⟩
  ext r
  rw [←D.sourceOrbit_hermitian_selected_section_kernel h d s r]
  constructor
  · intro hr b
    have hh := congrArg (fun t : MulAut (B₀ ⧸ U.subgroupOf B₀) =>
      t (QuotientGroup.mk' (U.subgroupOf B₀) b)) (MonoidHom.mem_ker.mp hr)
    rw [hf] at hh
    have hh := QuotientGroup.eq_iff_div_mem.mp hh
    change ((r : G) * (b : G) * (r : G)⁻¹) / (b : G) ∈ U at hh
    simpa only [commutatorElement_def,div_eq_mul_inv] using hh
  · intro hr
    apply MonoidHom.mem_ker.mpr
    ext b
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf B₀) b
    rw [hf]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((r : G) * (b : G) * (r : G)⁻¹) / (b : G) ∈ U
    simpa only [commutatorElement_def,div_eq_mul_inv] using hr b

/-- The literal tensor selection now also discharges the B/U kernel input
of the normalizer's product-action argument. -/
theorem sourceOrbit_hermitian_tensor_selected_section_kernel
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
    (hw : 0 < globalW D.sourceOrbit T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        let U := D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
        let R := Chapter8.Section02.Normalizer.localResidual L U
        rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
          U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
          R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
          Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
          (∀ r : R, (∀ b : ↥(D.sourceOrbit ⊓ I.pCoreIn 2), ⁅(r : G),(b : G)⁆ ∈ U) ↔
            r ∈ pCore 2 R) ∧
          ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
            (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
            R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
            IsQuasisimple (K ⧸ pCore 2 K) ∧
            ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) ∧
            let B₀ := D.sourceOrbit ⊓ I.pCoreIn 2
            ∃ hRB : R ≤ normalizer (B₀ : Set G),
              ∃ hU : (U.subgroupOf B₀).Normal, letI := hU
                ∃ f : R →* MulAut (B₀ ⧸ U.subgroupOf B₀),
                  f.ker = pCore 2 R ∧
                  ∀ (r : R) (b : B₀), f r (QuotientGroup.mk' (U.subgroupOf B₀) b) =
                    QuotientGroup.mk' (U.subgroupOf B₀)
                      (B₀.normalizerMonoidHom (inclusion hRB r) b) := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_pair_normalizer
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP⟩ := hK
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    D.sourceOrbit_hermitian_selected_section_kernel h.toHypothesis1221 d s,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,
    D.sourceOrbit_hermitian_selected_section_action h.toHypothesis1221 d s (le_sup_left.trans hRP)⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
