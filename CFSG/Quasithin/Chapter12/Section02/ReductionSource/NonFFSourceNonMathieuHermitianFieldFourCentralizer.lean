module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourLevi
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCentralizer
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The original Hermitian centralizer and containing C-component

For the canonical rank-four subgroup U, the full component centralizer
C_L(U) is solvable and its quotient by C_L(V) is the literal plane group
of order sixteen. The residual N_L(U)^∞ is a C-component of N_{N_G(L)}(U).
These statements apply to the whole zero-closure fixed subgroup and to
every parameter-one selection, with the original module and Sylow retained.

The half-field tensor supplies such U without an extra selection premise.
Its normalization by the original Sylow and source 1.2.4 then construct
an actual normal C-component of N_G(U) containing N_L(U)^∞. The kernel's
equality with the two-core, quasisimplicity of the containing component's
two-core quotient, zero-closure exclusion and the later argument through
8.2.13 remain to be proved.

The proof-only import reuses the original component action formula.
Source: Aschbacher--Smith H.4.6(2), 8.2.5--6 and the paragraph before
8.2.7, printed pp.382,716--717, using 1.2.4, printed p.505,
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

private theorem original_plane_centralizer
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
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      ∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf
          (L ⊓ centralizer (U : Set G))).Normal,
        Nonempty (((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf
            (L ⊓ centralizer (U : Set G))) ≃* UnipotentRadicals.plane 1) ∧
        IsElementaryAbelian 2 ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) ∧
        Nat.card ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) = 16 := by
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

  have hL : (⊤ : Subgroup L).IsCComponent := by
    have hh := h.maximal_faithful.1.1.1.subgroupOf_of_le (K := L) le_rfl le_sup_left
    simpa only [subgroupOf_self] using hh
  exact ⟨field_four_fixed_centralizer_solvable D.sourceOrbit L U hL
      (hU ▸ inf_le_left) D.sourceOrbit_component_normalizes e q hq heq hmark,
    field_four_fixed_residual_relative_component D.sourceOrbit L U hL
      (hU ▸ inf_le_left) D.sourceOrbit_component_normalizes e q hq heq hmark,
    field_four_fixed_centralizer_quotient D.sourceOrbit L U
      (hU ▸ inf_le_left) D.sourceOrbit_component_normalizes e q hq heq hmark⟩

/-- The full zero-closure fixed subgroup has solvable component centralizer,
with its exact plane quotient and relative C-component residual. -/
theorem sourceOrbit_hermitian_zero_fixed_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      ∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf
          (L ⊓ centralizer (U : Set G))).Normal,
        Nonempty (((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf
            (L ⊓ centralizer (U : Set G))) ≃* UnipotentRadicals.plane 1) ∧
        IsElementaryAbelian 2 ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) ∧
        Nat.card ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) = 16 := by
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨c,hc⟩ := (field_four_zero_closure_quotient D.sourceOrbit
    (D.hermitianOrbitCoordinates 1 d) j hj he T D.sourceOrbit_weakClosure_setup
    (D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon) hr hm hw).1
  exact D.original_plane_centralizer h.toHypothesis1221 d j he hcomp _ U
    ((indexedWeakClosure_le _ _ _).trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc

/-- The same centralizer and component statements hold on every original
parameter-one selection, without a new r-bound. -/
theorem sourceOrbit_hermitian_selected_fixed_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      ∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf
          (L ⊓ centralizer (U : Set G))).Normal,
        Nonempty (((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf
            (L ⊓ centralizer (U : Set G))) ≃* UnipotentRadicals.plane 1) ∧
        IsElementaryAbelian 2 ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) ∧
        Nat.card ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) = 16 := by
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  obtain ⟨_,hAT,_,_,_,_,_,_,_,c,hc⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  exact D.original_plane_centralizer h d j he hcomp A U
    (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes) rfl c hc
/-- The original half-field tensor supplies the exact component-centralizer
quotient and C-component placement at a Sylow-normal rank-four subgroup.
Both weak-closure branches remain. -/
theorem sourceOrbit_hermitian_tensor_fixed_centralizer
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
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
          (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
      ∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf
          (L ⊓ centralizer (U : Set G))).Normal,
        Nonempty (((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf
            (L ⊓ centralizer (U : Set G))) ≃* UnipotentRadicals.plane 1) ∧
        IsElementaryAbelian 2 ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) ∧
        Nat.card ((L ⊓ centralizer (U : Set G) : Subgroup G) ⧸
          (centralizer (D.sourceOrbit : Set G)).subgroupOf (L ⊓ centralizer (U : Set G))) = 16 := by
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
      D.sourceOrbit_hermitian_zero_fixed_centralizer h hmany hV hnon d hw⟩
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
      D.sourceOrbit_hermitian_selected_fixed_centralizer h.toHypothesis1221 d s⟩

/-- The original Sylow-normal fixed subgroup lifts the relative residual
into an actual normal C-component of its full ambient normalizer. -/
theorem sourceOrbit_hermitian_fixed_overcomponent
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hUne : U ≠ ⊥)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hR : (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
      (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent) :
    ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
      (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
      (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype ≤ K ∧
      normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let N := normalizer (U : Set G)
  let M := normalizer (L : Set G) ⊓ N
  have hRN : R ≤ N := (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right
  have hRM : R ≤ M := (Chapter8.Section02.Normalizer.localResidual_le L U).trans
    (inf_le_inf_right _ L.le_normalizer)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    Chapter8.Section02.Normalizer.normalizes_localResidual L U T D.sylow_normalizes_component hTU
  have hRTM : R ⊔ (T : Subgroup G) ≤ M := sup_le hRM
    (le_inf D.sylow_normalizes_component hTU)
  have hlocal : R ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hR.subgroupOf_of_le le_sup_left hRTM,?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · have hUQ := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
        ((hUV.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans
          (show (T : Subgroup G) ≤ R ⊔ (T : Subgroup G) from le_sup_right))
        (sup_le hRN hTU)
      exact ne_bot_of_le_ne_bot hUne hUQ
  let S := T.subtype hTU
  have hloc : R.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTU hRN).mp ⟨hRN,hlocal⟩
  have hSN : (S : Subgroup N) ≤ normalizer (R.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hRN]
    exact comap_mono hTR
  have hNH : N ∈ Chapter1.H G := ne_bot_of_le_ne_bot hUne
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) U.le_normalizer le_rfl)
  obtain ⟨K,⟨hK,hRK,hn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hNH) S hloc hSN
  let K' := K.map N.subtype
  have hKN : K' ≤ N := map_subtype_le _
  have hsub : K'.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  refine ⟨K',hKN,hsub.symm ▸ hK,?_,?_⟩
  · intro x hx
    have hxR : x ∈ R := hx
    let y : N := ⟨x,hRN hxR⟩
    have hy : y ∈ R.subgroupOf N := hxR
    exact mem_map_of_mem N.subtype (hRK hy)
  · exact (normal_subgroupOf_iff_le_normalizer hKN).mp (hsub.symm ▸ hn)

/-- The half-field tensor supplies a normal C-component in the full
normalizer of the same rank-four subgroup; no overcomponent input remains. -/
theorem sourceOrbit_hermitian_tensor_local_component
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
        Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
          (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
            (L ⊓ normalizer (U : Set G)).subtype ≤ K ∧
          normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hsol,hR,_⟩ := D.sourceOrbit_hermitian_tensor_fixed_centralizer
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  let := hU
  have hUne : U ≠ ⊥ := by
    intro hz
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  exact ⟨hn,hB,U,hU,hUV,hu,hTU,hsol,
    D.sourceOrbit_hermitian_fixed_overcomponent h.toHypothesis1221 U hUV hUne hTU hR⟩

end
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
