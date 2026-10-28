module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeComponent
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.RankSieve.SmallRows.LocalActions

/-!
# Original parabolic control in the M24-code row

The original selected pair generates H with T. The relative normalizer
residual centralizes the centralizer of the original fixed four-space
modulo its two-core, so O²(H) acts trivially on the full triple-A6 quotient.
The common Sylow places O₂(L_U)U inside O₂(H). Strong quasithinness of the
same normalizer then bounds the three- and five-ranks of H by one.

The cubic centre is retained throughout: the three-rank bound does not
assert that H is a three-prime group. The stronger exclusion in 8.2.9 and
the earlier code tensor calculation remain separate obligations.
Source: Aschbacher--Smith 8.2.8(2), opening of 8.2.9, printed pp.719--720,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode Chapter7.NormalizedSource
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer Chapter8.Section02.Normalizer.ParabolicReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original code marking constructs the selected pair, the parabolic's
literal quotient action, its local-core containment and odd-rank bounds. -/
theorem sourceOrbit_m24_code_parabolic_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let R := localResidual L U
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank (inducedAutomizer D.sourceOrbit A) = 6 ∧ rank U = 4 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
      R ≤ normalizer (I : Set G) ∧ R ≤ normalizer (I.pCoreIn 2 : Set G) ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      ⁅(pResidual 2 H).map H.subtype,R⁆ ≤ R.pCoreIn 2 ∧
      R.pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 ∧
      primeRank 3 H ≤ 1 ∧ primeRank 5 H ≤ 1 ∧ generationParameter H ≤ 2 ∧
      ∃ hHR : H ≤ normalizer (R : Set G),
        pResidual 2 H ≤ ((pCoreJoinAction 2 hHR).comp (inclusion le_sup_right)).ker ∧
        ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
          (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧ R ≤ K ∧
          normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
          IsQuasisimple (K ⧸ pCore 2 K) ∧ K.pCoreIn 2 ≤ T ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
          R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,⟨e⟩,hcomm,hRI,hRP,hK⟩ :=
    D.sourceOrbit_m24_code_component_pair_of_many h hmany hV hq hnon a E hE hH
  let A := offenderNormalizer D.sourceOrbit i.val⁻¹
  let U := D.sourceOrbit ⊓ centralizer (A : Set G)
  let R := localResidual L U
  have hgen := selected_generates_hstar s hH
  have hHN : H ≤ normalizer (U : Set G) := by
    rw [←hgen]
    exact sup_le (hIC.trans (Subgroup.centralizer_le_normalizer _)) hTU
  have hUne : U ≠ ⊥ := by
    intro hz
    change rank U = 4 at hU
    rw [hz,Representation.BinaryOffender.rank_bot] at hU
    omega
  have hlocal : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hUne,(IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le inf_le_left,rfl⟩
  have hjoin : H ⊔ R ≤ normalizer (U : Set G) :=
    sup_le hHN ((localResidual_le L U).trans inf_le_right)
  have hj (p : ℕ) (hp : p.Prime) (ho : Odd p) :
      primeRank p (H ⊔ R : Subgroup G) ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective p (inclusion hjoin) (inclusion_injective hjoin)).trans
      ((h.simpleQTKE.twoLocal_sqtk hlocal).stronglyQuasithin p hp ho)
  have hIM : ¬ I ≤ normalizer (L : Set G) := by
    intro hi
    apply hH.1.2
    rw [←hgen]
    exact sup_le hi D.sylow_normalizes_component
  have h3 : primeRank 3 H ≤ 1 :=
    RankSieve.three_rank_le_one_of_local_model T L (normalizer (L : Set G)) H I U
      hH s.family.le_ambient hIM hIC D.sylow_normalizes_component hTU hcomm e
      (Or.inr ⟨Hexacode.even_center_card.le,Hexacode.two_le_primeRank_even⟩)
      (hj 3 (by decide) (by decide))
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h5model : 1 ≤ primeRank 5 Atlas.Codes.HexEvenAutomorphisms := by
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card'
      (G := Atlas.Codes.HexEvenAutomorphisms) 5 (by rw [Atlas.Codes.hexEven_card]; decide)
    let : IsElementaryAbelian 5 (zpowers x) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [hx] using pow_orderOf_eq_one x)
    exact IsElementaryAbelian.primeRank_ge_of_card (zpowers x)
      (by simpa only [Nat.card_zpowers,pow_one] using hx)
  have h5 : primeRank 5 H ≤ 1 :=
    RankSieve.odd_rank_le_one_of_local_model T L (normalizer (L : Set G)) H I U
      hH s.family.le_ambient hIM hIC D.sylow_normalizes_component hTU hcomm
      (by decide) e (by rw [Hexacode.even_center_card]; decide) h5model
      (hj 5 (by decide) (by decide))
  have hQT : R.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 R).le_sylow_of_normalized T
      ((normalizes_localResidual L U (T : Subgroup G) D.sylow_normalizes_component hTU).trans
        (normalizer_le_normalizer_characteristic_image R (pCore 2 R)))
  have hUH : R.pCoreIn 2 ⊔ U ≤ H.pCoreIn 2 :=
    RankSieve.SmallRows.localCore_join_le_parabolicCore L H I U (T : Subgroup G)
      hgen T.isPGroup' hIC D.sylow_normalizes_component hTU hQT
      (inf_le_left.trans D.sourceOrbit_weakClosure_setup.le_sylow) hcomm
  have hn := (D.sourceOrbit_mathieu_generation_bounds h hmany hV
    (Or.inr (Or.inr (Or.inr hq))) hnon hH).2.1
  refine ⟨I,i,S,s,hw,hOff,hfix,hker,hIC,hr,hU,hUT,hTU,⟨e⟩,hcomm,hRI,hRP,
    hgen,hHN,residual_centralizes H I (T : Subgroup G) U hgen T.isPGroup' hIC hTU,
    RankSieve.residual_commutator_le_localCore L H I (T : Subgroup G) U
      hgen T.isPGroup' hIC hTU hcomm,hUH,h3,h5,hn,
    RankSieve.normalizes_localResidual_of_generation L H I (T : Subgroup G) U
      hgen hIC D.sylow_normalizes_component hTU hcomm,?_,hK⟩
  exact RankSieve.residual_fixes_localCore_quotient L H I (T : Subgroup G) U
    hgen T.isPGroup' hIC D.sylow_normalizes_component hTU hcomm

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
