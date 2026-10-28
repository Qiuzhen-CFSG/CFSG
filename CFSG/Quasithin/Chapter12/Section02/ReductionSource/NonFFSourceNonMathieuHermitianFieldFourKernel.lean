module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCentralizer
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourKernel
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The original Hermitian residual kernel

The half-field tensor supplies the same rank-four subgroup used in the
normalizer construction. Its residual has pointwise centralizer exactly
its two-core, and its literal two-core quotient is SL₂(4). We apply the
central-cover argument on both original weak-closure branches, retaining
the chosen module, original Sylow and original residual embeddings.

This proves the Hermitian kernel clause of 8.2.6(3). Quasisimplicity of the
containing component's two-core quotient in 8.2.7, zero-closure exclusion
and the remaining argument through 8.2.13 are still required. The proof-only
coordinate import unfolds the original component automizer for its conjugation
formula; it does not change the public coordinate boundary.
Source: Aschbacher--Smith H.4.6(2) and 8.2.6(3), printed pp.382,717,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem original_plane_residual_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (j : Automizer D.sourceOrbit →* binaryNormalizer 1)
    (he : ∀ a v, D.hermitianOrbitCoordinates 1 d
      (automizerRepresentation D.sourceOrbit a v) =
        overgroupAction 1 (binaryNormalizer 1) (j a) (D.hermitianOrbitCoordinates 1 d v))
    (hcomp : ∀ l : L, (j (D.hermitianComponentAutomizer l)).val =
      (d.groupEquiv (D.orbitComponentHom l)).val)
    (P U : Subgroup G) [IsElementaryAbelian 2 U]
    (hP : P ≤ normalizer (D.sourceOrbit : Set G))
    (hU : U = D.sourceOrbit ⊓ centralizer (P : Set G))
    (c : Cover 1) (hc : ((inducedAutomizer D.sourceOrbit P).map
      ((binaryNormalizer 1).subtype.comp j)).map
        (MulAut.conj (binaryActionHom 1 c)).toMonoidHom = UnipotentRadicals.plane 1) :
    let R := Chapter8.Section02.Normalizer.localResidual L U
    R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) := by
  let z := binaryActionHom 1 c
  let z' : binaryImage 1 := ⟨z,⟨c,rfl⟩⟩
  let e := (D.hermitianOrbitCoordinates 1 d).trans z
  let q := (MulAut.conj z').toMonoidHom.comp
    (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  have hq : Function.Surjective q := (MulAut.conj z').surjective.comp
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
  let l := (MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)
  have hl (a : Automizer D.sourceOrbit) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit a v) = l a (e v) := by
    change z (D.hermitianOrbitCoordinates 1 d (automizerRepresentation D.sourceOrbit a v)) =
      z ((j a).val (z.symm (z (D.hermitianOrbitCoordinates 1 d v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have him : (inducedAutomizer D.sourceOrbit P).map l = UnipotentRadicals.plane 1 := by
    rw [←map_map]
    exact hc
  have heq (a : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes a)) v) = (q a).val (e v) := by
    change e (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer a) v) = _
    rw [hl]
    change z ((j (D.hermitianComponentAutomizer a)).val (z.symm (e v))) =
      z ((d.groupEquiv (D.orbitComponentHom a)).val (z.symm (e v)))
    exact congrArg (fun t : (Space 1 ≃ₗ[ZMod 2] Space 1) => z (t (z.symm (e v)))) (hcomp a)
  have hmark (v : Additive D.sourceOrbit) : (v.toMul : G) ∈ U ↔
      e v ∈ fixedSpace (UnipotentRadicals.ambientAction 1) (UnipotentRadicals.plane 1) := by
    rw [hU]
    constructor
    · intro hv
      have hfix := (mem_fixedSpace_inducedAutomizer D.sourceOrbit P hP v).mpr hv.2
      intro a
      have ha : a.val ∈ (inducedAutomizer D.sourceOrbit P).map l := by
        rw [him]
        exact a.property
      obtain ⟨x,hx,hxa⟩ := ha
      change a.val (e v) = e v
      calc
        a.val (e v) = l x (e v) := congrArg (fun t : (Space 1 ≃ₗ[ZMod 2] Space 1) => t (e v)) hxa.symm
        _ = e (automizerRepresentation D.sourceOrbit x v) := (hl x v).symm
        _ = e v := congrArg e (hfix ⟨x,hx⟩)
    · intro hv
      refine ⟨v.toMul.property,?_⟩
      apply (mem_fixedSpace_inducedAutomizer D.sourceOrbit P hP v).mp
      intro a
      apply e.injective
      change e (automizerRepresentation D.sourceOrbit a.val v) = e v
      rw [hl]
      exact hv ⟨l a.val,him ▸ mem_map_of_mem l a.property⟩

  let := h.quasisimple
  have hk : pCore 2 L ≤ q.ker := by
    intro x hx
    have hh : D.orbitComponentHom x = 1 := D.orbitComponentHom_kills_core h hx
    exact (congrArg (MulAut.conj z')
      ((congrArg d.groupEquiv hh).trans (map_one d.groupEquiv))).trans
        (map_one (MulAut.conj z'))
  exact field_four_fixed_residual_kernel D.sourceOrbit L U
    (hU ▸ inf_le_left) D.sourceOrbit_component_normalizes e q hq hk heq hmark

/-- The original zero-closure fixed subgroup has the literal residual
centralizer equal to its two-core and quotient SL₂(4). -/
theorem sourceOrbit_hermitian_zero_fixed_residual_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) := by
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨c,hc⟩ := (field_four_zero_closure_quotient D.sourceOrbit
    (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw).1
  exact D.original_plane_residual_kernel h.toHypothesis1221 d j he hcomp _ U
    ((indexedWeakClosure_le _ _ _).trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc

/-- Every original parameter-one selection has the same residual kernel
and quotient, with no additional rank or kernel hypothesis. -/
theorem sourceOrbit_hermitian_selected_fixed_residual_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) := by
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  obtain ⟨_,hAT,_,_,_,_,_,_,_,c,hc⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  exact D.original_plane_residual_kernel h d j he hcomp A U
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc
/-- The actual half-field tensor gives the residual centralizer–two-core
identity and SL₂(4) quotient at an original Sylow-normal rank-four subgroup.
This establishes the Hermitian clause of 8.2.6(3) on both closure branches. -/
theorem sourceOrbit_hermitian_tensor_residual_kernel
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
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    n = 1 ∧ B.degree = 2 ∧
      ∃ U : Subgroup G, ∃ hU : IsElementaryAbelian 2 U, letI := hU
        U ≤ D.sourceOrbit ∧ rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
        let R := Chapter8.Section02.Normalizer.localResidual L U
        R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
        Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  by_cases hw : globalW D.sourceOrbit T = 0
  · let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let := hU
    have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
    have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
    obtain ⟨hu,hUT,_⟩ := field_four_zero_closure_fixed D.sourceOrbit
      (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
      (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw
    obtain ⟨hk,heq⟩ := D.sourceOrbit_hermitian_zero_fixed_residual_kernel h hmany hV hnon d hw
    obtain ⟨hsol,hR,_⟩ := D.sourceOrbit_hermitian_zero_fixed_centralizer h hmany hV hnon d hw
    have hUne : U ≠ ⊥ := by
      intro hz
      have hu' : rank U = 4 := hu
      rw [hz,Representation.BinaryOffender.rank_bot] at hu'
      omega
    exact ⟨U,hU,inf_le_left,hu,hUT,hk,heq,hsol,
      D.sourceOrbit_hermitian_fixed_overcomponent h.toHypothesis1221 U inf_le_left hUne hUT hR⟩
  · have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
      refine ⟨B,C,⟨eQ⟩,?_⟩
      dsimp only
      rw [hdegree]
      exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
    obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
    obtain ⟨_,I,i,S,s⟩ := D.sourceOrbit_hermitian_tensor_selected_of_positive
      h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel (pos_iff_ne_zero.mpr hw) hH
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let hU : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    let := hU
    obtain ⟨_,_,_,hu,_,_,hUT,_⟩ := selected_one_fixed_subgroup s
      D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
    obtain ⟨hk,heq⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s
    obtain ⟨hsol,hR,_⟩ := D.sourceOrbit_hermitian_selected_fixed_centralizer h.toHypothesis1221 d s
    have hUne : U ≠ ⊥ := by
      intro hz
      have hu' : rank U = 4 := hu
      rw [hz,Representation.BinaryOffender.rank_bot] at hu'
      omega
    exact ⟨U,hU,inf_le_left,hu,hUT,hk,heq,hsol,
      D.sourceOrbit_hermitian_fixed_overcomponent h.toHypothesis1221 U inf_le_left hUne hUT hR⟩


end
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
