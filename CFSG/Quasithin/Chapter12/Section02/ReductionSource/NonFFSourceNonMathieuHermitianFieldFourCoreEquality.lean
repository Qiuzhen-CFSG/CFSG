module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCoverSource
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCoreSupplement
public import Theory.GroupTheory.CoreCommutatorSupplement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The full original Hermitian two-core is V

The selected plane actor A supplements O₂(R) modulo O₂(LT), where
R = N_L(U)^∞. Since R normalizes the pair core, it normalizes VA, and
[O₂(LT),R] lies in V. Hence [O₂(R),R] lies in VA. The actual central-cover
calculation puts O₂(L) in [O₂(R),R]V, and C_A(V) ≤ V then forces O₂(L) ≤ V.
The reverse containment is part of the original chosen-module setup.

The tensor application uses the same selected pair throughout: the proved
H-star solvability supplies VA-normalization for that pair, while its full
parabolic construction supplies R-normalization. No central-kernel,
commutator, or normalization premise remains in the tensor export.

The internal coordinate import reuses the action formula on original
representatives. Source: Aschbacher–Smith 8.2.10(3), printed p.721,
refs/quasithin.pdf. The positive-closure central-involution argument and
the zero weak-closure branch remain to be completed.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- Source 8.2.10(3) for the actual selected pair. The parabolic normalization
and VA normalization are supplied by the preceding source arguments. -/
theorem sourceOrbit_hermitian_selected_core_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hRP : Chapter8.Section02.Normalizer.localResidual L (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) ≤
        normalizer (I.pCoreIn 2 : Set G))
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G)) :
    L.pCoreIn 2 = D.sourceOrbit := by
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨hcomm,hcommL⟩ := D.sourceOrbit_hermitian_selected_core_commutators
    h.toHypothesis1221 hV s hTVA
  have hgen := (D.sourceOrbit_hermitian_selected_cover_parabolics
    h hmany hV hnon hcomm hcommL d s).2.2
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,hAT,_,_,_,_,hTU,_,_,c,hc⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let z := binaryActionHom 1 c
  let z' : binaryImage 1 := ⟨z,⟨c,rfl⟩⟩
  let e := (D.hermitianOrbitCoordinates 1 d).trans z
  let f := (MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)
  have hf : Function.Injective f := (MulAut.conj z).injective.comp
    ((binaryNormalizer 1).subtype_injective.comp hj)
  have he' (a : Automizer D.sourceOrbit) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit a v) = f a (e v) := by
    change z (D.hermitianOrbitCoordinates 1 d (automizerRepresentation D.sourceOrbit a v)) =
      z ((j a).val (z.symm (z (D.hermitianOrbitCoordinates 1 d v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have hA : (inducedAutomizer D.sourceOrbit A).map f = UnipotentRadicals.plane 1 := by
    rw [←map_map]
    exact hc
  have hRL : R ≤ L := (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_left
  have hXL : R.pCoreIn 2 ≤ L := (pCoreIn_le 2 R).trans hRL
  have hX : (inducedAutomizer D.sourceOrbit (R.pCoreIn 2)).map f ≤ binaryImage 1 := by
    rintro _ ⟨a,⟨b,hb,rfl⟩,rfl⟩
    let l : L := ⟨b,hXL hb⟩
    have hh := hcomp l
    change (j (D.sourceOrbit.normalizerMonoidHom.rangeRestrict b)).val =
      (d.groupEquiv (D.orbitComponentHom l)).val at hh
    change z * (j (D.sourceOrbit.normalizerMonoidHom.rangeRestrict b)).val * z⁻¹ ∈ binaryImage 1
    rw [hh]
    exact (binaryImage 1).mul_mem ((binaryImage 1).mul_mem z'.property
      (d.groupEquiv (D.orbitComponentHom l)).property) ((binaryImage 1).inv_mem z'.property)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    Chapter8.Section02.Normalizer.normalizes_localResidual L U (T : Subgroup G)
      D.sylow_normalizes_component hTU
  have hXT : R.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 R).le_sylow_of_normalized T
      (hTR.trans (normalizer_le_normalizer_characteristic_image R (pCore 2 R)))
  have hCQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) ≤ Q := by
    rw [D.sourceOrbit_eq]
    exact (D.orbit_centralizer h.toHypothesis1221).le
  have hker := (D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s).1
  have hXC : R.pCoreIn 2 ≤ centralizer (U : Set G) := hker ▸ inf_le_right
  have hsup : R.pCoreIn 2 ≤ A ⊔ Q := marked_plane_centralizer_supplement
    D.sourceOrbit A (R.pCoreIn 2) (T : Subgroup G) Q hAT hXT
    D.sourceOrbit_weakClosure_setup.normalizes hCQ e f hf he' hA hX hXC
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
      pCoreIn_le_sylow _ (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))
  have hW : D.sourceOrbit ⊔ A = D.sourceOrbit ⊔ I.pCoreIn 2 := by
    rw [selected_one_core_product s,←sup_assoc,sup_of_le_left (show
      D.sourceOrbit ⊓ I.pCoreIn 2 ≤ D.sourceOrbit from inf_le_left)]
  have hRW : R ≤ normalizer ((D.sourceOrbit ⊔ A : Subgroup G) : Set G) := by
    rw [hW]
    exact (le_inf (hRL.trans D.sourceOrbit_component_normalizes) hRP).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hLQ : L.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hAC : A ⊓ centralizer (D.sourceOrbit : Set G) ≤ D.sourceOrbit := by
    have hh := (selected_core_actor_data s D.sourceOrbit_weakClosure_setup).2.2.2.1
    exact hh.le.trans inf_le_left
  have hle := core_le_module_of_parabolic_commutator D.sourceOrbit A Q (R.pCoreIn 2) R
    (L.pCoreIn 2) (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes)
    (hQT.trans hTVA) hRW hsup ((commutator_mono le_rfl hRL).trans hcomm.le)
    hgen (hLQ.trans hQC) hAC
  exact le_antisymm hle (hV ▸ D.le_componentCore)

/-- The original half-field tensor discharges all selected-pair premises
and identifies V with the whole original component two-core. -/
theorem sourceOrbit_hermitian_tensor_core_eq
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
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧ V = L.pCoreIn 2 := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  have hsol := D.sourceOrbit_hermitian_tensor_hstar_solvable
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  obtain ⟨hn,hB,hw1,I,i,S,s,_,_,_,_,_,K,_,_,_,_,_,_,_,hRP,_,_,_,_,hsieve,_,_,_,_,_,_,
    h3,h5,_,hinter,himage,_⟩ := D.sourceOrbit_hermitian_tensor_selected_parabolic_core
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  obtain ⟨_,_,_,_,hTVA⟩ := selected_one_solvable_parabolic s h28 hH hsol
    D.sourceOrbit_weakClosure_setup.normalizes h3 h5 (hinter ▸ inf_le_right) himage hsieve
  subst hn
  exact ⟨rfl,hB,hw1,hV.trans (D.sourceOrbit_hermitian_selected_core_eq
    h hmany hV hnon d s (le_sup_left.trans hRP) hTVA).symm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
