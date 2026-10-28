module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourQuasisimple
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourExtraCenter

/-!
# The literal Hermitian pair and its containing component

The four-space in the earlier quasisimplicity endpoint was existential.
Here the A.3.6 argument is applied to each specified canonical four-space:
the original parameter-one fixed subgroup, or the fixed subgroup of the
zeroth weak closure. The existing natural and elementary-radical exclusions,
actual extraspecial H-star placement and whole noncubic normalizer control
discharge every alternative, retaining the full two-core quotient.

On the selected branch, the same centralizer commutator bound makes
R O₂(K) normalize both I = ⟨V,V^h⟩ and P = O₂(I). The final tensor
application constructs the pair and its containing component in each
original H-star group. No component or pair-action hypothesis is added to
that application. The source convention V^h = h⁻¹ V h is retained.

The proof-only import reuses the existing internal extraspecial-center
assembly. Zero weak-closure exclusion, the kernel and tensor identification
on P/U, and the remaining 8.2.8--13 arguments remain separate obligations.
Source: Aschbacher--Smith 8.2.7 and the opening of 8.2.8(4), printed
pp.717--718, refs/quasithin.pdf (1 March 2004 manuscript).
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
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem quasisimple_at_fixed_four_space
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    (U K : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hu : rank U = 4)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hKU : K ≤ normalizer (U : Set G))
    (hK : (K.subgroupOf (normalizer (U : Set G))).IsCComponent)
    (hRK : Chapter8.Section02.Normalizer.localResidual L U ≤ K)
    (hNK : normalizer (U : Set G) ≤ normalizer (K : Set G))
    (hR : Nonempty (((Chapter8.Section02.Normalizer.localResidual L U) ⧸
      pCore 2 (Chapter8.Section02.Normalizer.localResidual L U)) ≃* SL(2,E 1)))
    (hker : Chapter8.Section02.Normalizer.localResidual L U ⊓ centralizer (U : Set G) =
      (Chapter8.Section02.Normalizer.localResidual L U).pCoreIn 2)
    (hnat : ¬ Chapter1.Section02.A36Natural (Chapter1.XiQuotient K))
    (hnel : ∀ (p : ℕ) (_ : Fact p.Prime),
      Chapter1.Section02.A36Nilpotent (Chapter1.XiQuotient K) →
      p ∣ Nat.card (fittingSubgroup (Chapter1.XiQuotient K)) →
      ¬ IsElementaryAbelian p (Chapter1.XiQuotient (Chapter1.XiP p K)))
    (hprime : ∀ (p : ℕ) (_ : Fact p.Prime), 3 < p → ∀ Z : Subgroup G,
      IsPGroup p Z → Z ≤ normalizer (L : Set G) →
      Z ≤ centralizer (U : Set G) → Z ≤ centralizer (D.sourceOrbit : Set G)) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧
      ⁅Chapter8.Section02.Normalizer.localResidual L U, centralizer (U : Set G)⁆ ≤
        (Chapter8.Section02.Normalizer.localResidual L U).pCoreIn 2 := by
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
    obtain ⟨_,hx,hcard,hexp⟩ := nilpotent_core_extraspecial_of_not_elementary K hnil p hd
      (hnel p inferInstance hnil hd)
    have hjoin := D.sourceOrbit_hermitian_extraspecial_radical_hstar h hs hrow
      U K hUV hu hTU hKU hK (hTU.trans hNK) hRK hR p hnil hd hx hcard
    have hgt := (Chapter1.RadicalStructure.radical_core (Or.inr hnil) hd).2.1
    let P : Sylow p (Chapter1.XiP p K) := Classical.choice inferInstance
    obtain ⟨hc,hcyc,hne,hplaced,hout,_⟩ := D.nilpotent_centers_at_four_space
      h hmany hV hnon hs hrow d U K hUV hu hTU hKU hK (hTU.trans hNK)
      hRK hR p hnil hd hx hcard hexp (hprime p inferInstance hgt) hjoin P
    let Y := (P : Subgroup (Chapter1.XiP p K)).map (Chapter1.XiP p K).subtype
    let Z := (center Y).map Y.subtype
    let : IsCyclic Z := hcyc
    have hZ : IsElementaryAbelian p Z := {
      exponent_dvd_p := hc ▸ Group.exponent_dvd_nat_card }
    exact hout (D.sourceOrbit_hermitian_field_four_oddActor_normalizer
      h hmany hV hnon d B eQ hfield hp hgt Z hne hZ hplaced)

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

/-- At every actual parameter-one selection, retain its literal fixed subgroup
and containing component, and obtain the pair and two-core actions of 8.2.8. -/
theorem sourceOrbit_hermitian_selected_component_pair_normalizer
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
    {H I K : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hKU : K ≤ normalizer (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G))).IsCComponent)
    (hRK : Chapter8.Section02.Normalizer.localResidual L (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) ≤ K)
    (hNK : normalizer (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G) : Set G) ≤
        normalizer (K : Set G)) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    IsQuasisimple (K ⧸ pCore 2 K) ∧ ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
      R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,hu,_,_,hTU,hIC,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨hker,hR⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s
  obtain ⟨hq,hcomm⟩ := D.quasisimple_at_fixed_four_space h hmany hV hnon hs hrow d B eQ hB
    U K inf_le_left hu hTU hKU hK hRK hNK hR hker
    (D.sourceOrbit_hermitian_selected_component_not_natural h hmany hV hs hnon
      B C eQ 1 hdegree hfield hmodel s hKU hK (hTU.trans hNK) hRK)
    (fun p hp hnil hd => by
      let := hp
      exact D.sourceOrbit_hermitian_selected_component_not_elementary_nilpotent
        h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel s hKU hK (hTU.trans hNK) hRK p hnil hd)
    (fun p hp hgt Z hZ hZM hZU => by
      let := hp
      exact D.sourceOrbit_hermitian_selected_prime_centralizer h hmany hV hnon d s Z hgt hZ hZM hZU)
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 K).le_sylow_of_normalized T
      ((hTU.trans hNK).trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  exact ⟨hq,hcomm,Chapter8.Section02.Normalizer.local_factor_normalizes_pair_and_core
    L K U I D.sourceOrbit T i.val i.property s.generate hIC hNK hQT
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes hcomm⟩

/-- Quasisimplicity and the full centralizer commutator bound at the literal
zeroth weak-closure fixed subgroup, with the original component retained. -/
theorem sourceOrbit_hermitian_zero_component_quasisimple
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
    (hw : globalW D.sourceOrbit T = 0)
    (K : Subgroup G)
    (hKU : K ≤ normalizer
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G))
    (hK : (K.subgroupOf (normalizer
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G))).IsCComponent)
    (hRK : Chapter8.Section02.Normalizer.localResidual L
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)) ≤ K)
    (hNK : normalizer
      (D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G) : Set G) ≤
        normalizer (K : Set G)) :
    let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    IsQuasisimple (K ⧸ pCore 2 K) ∧ ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨by decide,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary 1),hmodel⟩
  obtain ⟨hu,hTU,_⟩ := D.sourceOrbit_hermitian_zero_closure_fixed h hmany hV hnon d hw
  let U := D.sourceOrbit ⊓ centralizer (indexedWeakClosure D.sourceOrbit T 0 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨hker,hR⟩ := D.sourceOrbit_hermitian_zero_fixed_residual_kernel h hmany hV hnon d hw
  exact D.quasisimple_at_fixed_four_space h hmany hV hnon hs hrow d B eQ hB
    U K inf_le_left hu hTU hKU hK hRK hNK hR hker
    (D.sourceOrbit_hermitian_zero_component_not_natural h hmany hV hs hnon
      B C eQ 1 hdegree hfield hmodel hw K hKU hK (hTU.trans hNK) hRK)
    (fun p hp hnil hd => by
      let := hp
      exact D.sourceOrbit_hermitian_zero_component_not_elementary_nilpotent
        h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel hw K hKU hK (hTU.trans hNK) hRK p hnil hd)
    (fun p hp hgt Z hZ hZM hZU => by
      let := hp
      exact D.sourceOrbit_hermitian_zero_prime_centralizer h hmany hV hnon d hw Z hgt hZ hZM hZU)

/-- Construct the original selected pair and the containing component together.
No component, quasisimplicity or pair-normalization premise is required. -/
theorem sourceOrbit_hermitian_tensor_selected_pair_normalizer
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
          ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
            (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
            R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
            IsQuasisimple (K ⧸ pCore 2 K) ∧
            ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨hw1,I,i,S,s⟩ := D.sourceOrbit_hermitian_tensor_selected_of_positive
    h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel hw hH
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,hu,hUeq,_,hTU,_⟩ := selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup 1 (D.hermitianOrbitCoordinates 1 d) j hj he
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  obtain ⟨hker,hR⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h.toHypothesis1221 d s
  obtain ⟨_,hc,_⟩ := D.sourceOrbit_hermitian_selected_fixed_centralizer h.toHypothesis1221 d s
  obtain ⟨K,hKU,hK,hRK,hNK⟩ := D.sourceOrbit_hermitian_fixed_overcomponent
    h.toHypothesis1221 U inf_le_left hUne hTU hc
  exact ⟨hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,K,hKU,hK,hRK,hNK,
    D.sourceOrbit_hermitian_selected_component_pair_normalizer
      h hmany hV hs hnon B C eQ 1 hdegree hfield hmodel s hKU hK hRK hNK⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
