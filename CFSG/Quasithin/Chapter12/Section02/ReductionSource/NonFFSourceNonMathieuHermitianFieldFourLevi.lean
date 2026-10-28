module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourIntersection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourLevi
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The original field-four fixed subgroup and its SL₂(4) action

The marked plane radical determines a four-dimensional fixed subgroup on
the literal chosen orbit. Its component normalizer residual realizes the
faithful two-by-two Hermitian SL₂(4) action. Inner conjugation transports the
plane coordinates while preserving the original component, its residual,
the ambient automizer and the original Sylow subgroup. The entire residual
action image equals the marked SL₂(4) image.

This applies to the fixed subgroup of the whole zeroth weak closure and to
every parameter-one selection. The final half-field tensor application
constructs such a subgroup without a weak-closure or selection premise,
using the existing positive/zero dichotomy. It supplies the action input
for 8.2.6; identification of its centralizer kernel with its two-core,
component placement, zero exclusion and the terminal argument through
8.2.13 remain to be proved.

The proof-only import exposes the existing component-automizer formula;
its public definition and visibility are unchanged.
Source: Aschbacher--Smith H.4.6(2), 8.2.5--6, printed pp.382,716--717,
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

private theorem original_plane_action
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
    ∃ (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
      (f : SL(2,E 1) →* Automizer U), Function.Injective f ∧
        f.range = inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
          (L ⊓ normalizer (U : Set G)).subtype) ∧
        ∀ a u, b (automizerRepresentation U (f a) u) =
          OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
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
  apply field_four_fixed_subgroup_sl2_action D.sourceOrbit L U
    (hU ▸ inf_le_left) D.sourceOrbit_component_normalizes e q hq
  · intro a v
    change e (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer a) v) = _
    rw [hl]
    change z ((j (D.hermitianComponentAutomizer a)).val (z.symm (e v))) =
      z ((d.groupEquiv (D.orbitComponentHom a)).val (z.symm (e v)))
    exact congrArg (fun t : (Space 1 ≃ₗ[ZMod 2] Space 1) => z (t (z.symm (e v)))) (hcomp a)
  · intro v
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

/-- The whole zero-closure fixed subgroup carries the faithful Hermitian
SL₂(4) action of the original component normalizer residual. -/
theorem sourceOrbit_hermitian_zero_fixed_sl2_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    ∃ (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
      (f : SL(2,E 1) →* Automizer U), Function.Injective f ∧
        f.range = inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
          (L ⊓ normalizer (U : Set G)).subtype) ∧
        ∀ a u, b (automizerRepresentation U (f a) u) =
          OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨c,hc⟩ := (field_four_zero_closure_quotient D.sourceOrbit
    (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw).1
  exact D.original_plane_action d j he hcomp _ U
    ((indexedWeakClosure_le _ _ _).trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc

/-- The same literal SL₂(4) action is present on the fixed subgroup of
any parameter-one selection, without adding an r-bound. -/
theorem sourceOrbit_hermitian_selected_fixed_sl2_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    ∃ (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
      (f : SL(2,E 1) →* Automizer U), Function.Injective f ∧
        f.range = inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
          (L ⊓ normalizer (U : Set G)).subtype) ∧
        ∀ a u, b (automizerRepresentation U (f a) u) =
          OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  obtain ⟨_,hAT,_,_,_,_,_,_,_,c,hc⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  exact D.original_plane_action d j he hcomp A U
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc
/-- The literal half-field tensor supplies a rank-four subgroup normalized
by the original Sylow, with the faithful Hermitian SL₂(4) action realized
as the whole action image of the original component normalizer residual.
Both weak-closure branches remain. -/
theorem sourceOrbit_hermitian_tensor_fixed_sl2_action
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
        ∃ (b : Additive U ≃ₗ[ZMod 2] OrthogonalFourMinus.FiniteModel.Space 1)
          (f : SL(2,E 1) →* Automizer U), Function.Injective f ∧
            f.range = inducedAutomizer U ((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
          (L ⊓ normalizer (U : Set G)).subtype) ∧
            ∀ a u, b (automizerRepresentation U (f a) u) =
              OrthogonalFourMinus.FiniteModel.action 1 a (b u) := by
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
    exact ⟨U,hU,inf_le_left,hu,hUT,
      D.sourceOrbit_hermitian_zero_fixed_sl2_action h hmany hV hnon d hw⟩
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
    exact ⟨U,hU,inf_le_left,hu,hUT,
      D.sourceOrbit_hermitian_selected_fixed_sl2_action h.toHypothesis1221 d s⟩

end
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
