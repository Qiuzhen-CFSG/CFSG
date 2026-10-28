module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOrdinaryExclusion
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Equivalences
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# Quasisimplicity of the original four-space component

On the actual half-field tensor input, the earlier constructions give the
original Sylow-normal four-space and its containing normal C-component.
The complete A.3.6 alternatives are applied to its literal two-core
quotient. The natural alternative is already excluded. In the nilpotent
alternative, a Fitting prime gives an actual extraspecial Sylow center
with an escaping normalizer and the ordinary pushing-up configuration.
The ordinary J₄ exclusion proved in the companion module contradicts it.

Thus the same containing component has quasisimple two-core quotient.
The residual's full SL₂(4) quotient makes its action nontrivial, so the
perfect-component commutator argument also gives
[R, C_G(U)] ≤ O₂(R), with R = N_L(U)^∞.
Both weak-closure branches and all original actions and kernels are retained.
The zero-closure exclusion and the remaining 8.2.8--13 assembly are separate
obligations; this is not the final non-FF contradiction.

Source: Aschbacher--Smith 8.2.7 and 8.2.8(2), printed pp.717--718,
refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual tensor supplies a four-space and normal containing component
with quasisimple two-core quotient, together with the centralizer commutator
bound of 8.2.8(2). Both original weak-closure branches are included. -/
theorem sourceOrbit_hermitian_tensor_component_quasisimple
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
          R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧
          ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 := by
  obtain ⟨hn,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,hnat,hcores⟩ :=
    D.sourceOrbit_hermitian_tensor_nilpotent_center_pushingUp
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    (ρ := D.orbitRepresentation) (Q := D.orbitComponent) hs B C n hdegree hfield hmodel
  subst hn
  let := hU
  refine ⟨rfl,hB,U,hU,hUV,hu,hTU,hker,hR,hsol,K,hKU,hK,hRK,hNK,?_⟩
  have hUne : U ≠ ⊥ := by
    intro he
    rw [he,Representation.BinaryOffender.rank_bot] at hu
    omega
  have hlocal : K ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hK.subgroupOf_of_le le_sup_left (sup_le hKU hTU),?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · exact ne_bot_of_le_ne_bot hUne
        (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
          (hUV.trans (D.sourceOrbit_weakClosure_setup.le_sylow.trans le_sup_right))
          (sup_le hKU hTU))
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hlocal.2.2
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let X := Chapter1.radicalLocalImage (T : Subgroup G) K
  let ex : Chapter1.XiQuotient K ≃* X := Chapter1.radicalLocalQuotientEquiv hlocal
  let := pCore_isNilpotent (p := 2) (G := (K ⊔ (T : Subgroup G) : Subgroup G))
  have hX : X.IsCComponent := hlocal.1.map_quotient _
  have ha := Chapter1.Section02.proposition_1_2_1_four_earlier_conclusion hA36 hQ hlocal.1
  have hquasi : IsQuasisimple (K ⧸ pCore 2 K) := by
    by_contra hnot
    have hnotX : ¬ IsQuasisimple X := fun hx => hnot (hx.of_mulEquiv ex.symm)
    rcases Chapter1.RadicalStructure.nonsimple_radical ha hnotX with hna | hni
    · exact hnat (hna.of_mulEquiv ex.symm)
    have hnil := hni.of_mulEquiv ex.symm
    let : Nontrivial X := (nontrivial_iff_ne_bot _).mpr hX.ne_bot
    let : Nontrivial (Chapter1.XiQuotient K) := ex.symm.injective.nontrivial
    have hfit : Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) ≠ 1 := by
      intro hc
      have hg : generalizedFitting (Chapter1.XiQuotient K) = ⊥ := hnil.1.trans (card_eq_one.mp hc)
      have hh := Theory.GroupTheory.centralizer_generalizedFitting_le (Chapter1.XiQuotient K)
      have hbot : centralizer ((⊥ : Subgroup (Chapter1.XiQuotient K)) : Set (Chapter1.XiQuotient K)) = ⊤ := by
        ext g
        simp [mem_centralizer_iff]
      rw [hg,hbot] at hh
      exact top_ne_bot (le_antisymm hh bot_le)
    obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hfit
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨_,_,_,_,_,_,hcenters⟩ := hcores hnil p inferInstance hd
    let P : Sylow p (Chapter1.XiP p K) := Classical.choice inferInstance
    obtain ⟨_,_,_,_,_,_,hcase⟩ := hcenters P
    obtain ⟨J,H,W,hw,K',hK',_⟩ := hcase
    exact D.sourceOrbit_hermitian_no_ordinary_janko h hmany hV hnon d B eQ hB hw K' hK'

  let := hquasi
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKU).toMonoidHom) (subgroupOfEquivOfLe hKU).surjective
  let R := Chapter8.Section02.Normalizer.localResidual L U
  have hnontriv : ¬ R ≤ centralizer (U : Set G) := by
    intro hc
    have he : R = R.pCoreIn 2 := (inf_eq_left.mpr hc).symm.trans hker
    have ht : pCore 2 R = ⊤ := by
      apply map_injective R.subtype_injective
      simpa only [pCoreIn, ← MonoidHom.range_eq_map, range_subtype] using he.symm
    obtain ⟨e⟩ := hR
    have hcq : Nat.card (R ⧸ pCore 2 R) = 1 := by rw [ht]; simp
    have hcs : Nat.card SL(2,E 1) = 60 := by
      rw [BenderSuzuki.External.huppert614_card_specialLinearGroup]
      rw [card_E]
      norm_num
    have hec := Nat.card_congr e.toEquiv
    change Nat.card (R ⧸ pCore 2 R) = _ at hec
    omega
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  exact ⟨hquasi,Chapter8.Section02.Normalizer.localResidual_centralizer_commutator
    L K U (T : Subgroup G) hRK hKU hNK hnontriv hQT D.sylow_normalizes_component hTU⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
