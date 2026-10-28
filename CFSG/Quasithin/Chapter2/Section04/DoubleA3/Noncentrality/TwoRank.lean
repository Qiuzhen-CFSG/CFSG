module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.CommutingComponents
public import Theory.GroupTheory.NormalizerActionCore
public import Theory.GroupTheory.TwoLocalCoreObstruction
public import Theory.GroupTheory.AutomorphismSquareRank
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.SpecificGroups.Alternating.CommutingFourSixObstruction

/-!
# The faithful paired action and Sylow two-rank bound

The commuting component pair escapes the unique maximal two-local overgroup,
so adjoining the original Sylow group gives trivial two-core. An A₆ factor
would commute with the exchanged A₄ block and produce a forbidden rank-three
two-local subgroup. Thus the factor is PSL₃(2). The trivial two-core makes the
Sylow action on the pair faithful; the actual product equivalence and the
rank of Aut(PSL₃(2)) then give the bound four.

All groups, cubic blocks and actors are those selected by the original source.
The preceding component identification and layer statements remain explicit
inputs, supplied by 2.4.32–33.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, through m₂(T) ≤ 4.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The original contradiction gives the binary projective component and faithful
Sylow action of two-rank at most four. -/
theorem source_pair_two_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hE : K = (componentLayer (centralizer ({g.z₂} : Set G))).map
      (centralizer ({g.z₂} : Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({g.z₂} : Set G)) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL))
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    let J := K ⊔ Ks
    pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G) = ⊥ ∧
      Nonempty (K ≃* Matrix.PSL3Two.PSL) ∧
      (T : Subgroup G) ⊓ centralizer (J : Set G) = ⊥ ∧ primeRank 2 T ≤ 4 := by
  let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
  let J := K ⊔ Ks
  obtain ⟨hcentral,hdisj,hne,hTN,hxK,hxKs,hsK,hsKs,hsimple⟩ :=
    source_commuting_components c g K hK hE ho hfirst hmodel hcomm
  have hcore : pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G) = ⊥ := by
    rw [sup_comm]
    apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup (T : Subgroup G) J M hu
    exact fun h => d.outside (hfirst.trans (le_sup_left.trans h))
  have hbinary : Nonempty (K ≃* Matrix.PSL3Two.PSL) := by
    rcases hmodel with hA | hP
    · obtain ⟨eK⟩ := hA
      obtain ⟨eL⟩ := c.cubic_second.equiv_alternatingFour
      have hLs : c.L ≤ Ks := by
        change c.L ≤ K.map (MulAut.conj c.s⁻¹).toMonoidHom
        rw [←hsK,←c.exchange]
        exact map_mono hfirst
      exact (Theory.Quasithin.not_quasithin_of_commuting_a4_a6 c.L K eL eK
        (hLs.trans (le_centralizer_iff.mp hcentral)) hG.quasithin).elim
    · exact hP
  have hfix := inf_centralizer_eq_bot_of_sup_pCore_eq_bot (T : Subgroup G) J T.isPGroup' hTN hcore
  refine ⟨hcore,hbinary,hfix,?_⟩
  obtain ⟨eK⟩ := hbinary
  let : IsSimpleGroup K := hsimple
  let := hK.quasisimple
  have hZ : center K = ⊥ := by
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  have hAut : primeRank 2 (MulAut K) = 2 := by
    rw [primeRank_equiv 2 (MulAut.congr eK)]
    exact Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2) (by simp)
  obtain ⟨eP,heP⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K Ks hdisj hcentral
  let eS : K ≃* Ks := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom
    (MulAut.conj c.s⁻¹).injective
  let e : J ≃* K × K := eP.symm.trans ((MulEquiv.refl K).prodCongr eS.symm)
  let ρ : T →* MulAut J := J.normalizerMonoidHom.comp (inclusion hTN)
  have hf : Function.Injective ρ :=
    normalizer_action_injective_of_sup_pCore_eq_bot (T : Subgroup G) J T.isPGroup' hTN hcore
  have hr := (Theory.GroupTheory.primeRank_le_of_injective 2 ρ hf).trans_eq
    (primeRank_equiv 2 (MulAut.congr e))
  have hb := AutomorphismSquare.rank_bound hZ (by omega : 0 < primeRank 2 (MulAut K))
  rw [hAut] at hb
  exact hr.trans hb

end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality