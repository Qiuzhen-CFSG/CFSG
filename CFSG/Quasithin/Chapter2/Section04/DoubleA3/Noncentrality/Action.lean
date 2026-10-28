module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Noncentrality.TwoRank
public import Theory.GroupTheory.NormalizerActionCore

/-!
# The faithful action in chosen component coordinates

Multiplication identifies the commuting pair with the square of the chosen
PSL₃(2) model. The second coordinate is transported by the original exchange
actor, so both component embeddings retain their literal values. The whole
generated group acts faithfully: its centralizer kernel embeds in the
prime-group quotient and is killed by the trivial two-core.

Source: Aschbacher–Smith, Lemma 2.4.34, printed p.548, the identification of
I = KKˢT with its action on the component pair.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G}

/-- The faithful paired action, retaining a chosen first-component identification
and the original conjugation defining the second component. -/
theorem source_pair_action_of_equiv
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (c : SourcePairCoordinates d T) (g : SourceCentralizerGeometry c)
    (K : Subgroup G) (hK : IsComponentIn K (centralizer ({g.z₂} : Set G)))
    (hE : K = (componentLayer (centralizer ({g.z₂} : Set G))).map
      (centralizer ({g.z₂} : Set G)).subtype)
    (ho : pPrimeCore 2 (centralizer ({g.z₂} : Set G)) = ⊥)
    (hfirst : d.block.map d.H.subtype ≤ K)
    (hcomm : c.U₂ ≤ centralizer (K : Set G)) (eK : K ≃* Matrix.PSL3Two.SL) :
    let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
    let J := K ⊔ Ks
    let I := J ⊔ (T : Subgroup G)
    let eS := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom (MulAut.conj c.s⁻¹).injective
    ∃ e : J ≃* Matrix.PSL3Two.SL × Matrix.PSL3Two.SL,
      (∀ k : K, e (inclusion le_sup_left k) = (eK k,1)) ∧
      (∀ k : K, e (inclusion le_sup_right (eS k)) = (1,eK k)) ∧
      ∃ hn : I ≤ normalizer (J : Set G),
        let ρ := (MulAut.congr e).toMonoidHom.comp (J.normalizerMonoidHom.comp (inclusion hn))
        Function.Injective ρ ∧ ∀ j : J, ρ (inclusion le_sup_left j) = MulAut.conj (e j) := by
  let Ks := K.map (MulAut.conj c.s⁻¹).toMonoidHom
  let J := K ⊔ Ks
  let I := J ⊔ (T : Subgroup G)
  have hmodel : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL) :=
    Or.inr ⟨eK.trans Matrix.PSL3Two.equiv⟩
  obtain ⟨hc,hd,_,hTN,_⟩ := source_commuting_components c g K hK hE ho hfirst hmodel hcomm
  have hcore : pCore 2 I = ⊥ := by
    change pCore 2 (J ⊔ (T : Subgroup G) : Subgroup G) = ⊥
    rw [sup_comm]
    apply twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup (T : Subgroup G) J M hu
    exact fun h => d.outside (hfirst.trans (le_sup_left.trans h))
  obtain ⟨eP,hP⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K Ks hd hc
  let eS : K ≃* Ks := K.equivMapOfInjective (MulAut.conj c.s⁻¹).toMonoidHom
    (MulAut.conj c.s⁻¹).injective
  let e₂ : Ks ≃* Matrix.PSL3Two.SL := eS.symm.trans eK
  let e := eP.symm.trans (eK.prodCongr e₂)
  have hleft (k : K) : e (inclusion le_sup_left k) = (eK k,1) := by
    have hh : eP (k,1) = inclusion le_sup_left k := by
      apply Subtype.ext
      simpa only [coe_one,mul_one,coe_inclusion] using hP k 1
    change (eK.prodCongr e₂) (eP.symm (inclusion le_sup_left k)) = _
    rw [←hh,eP.symm_apply_apply]
    change (eK k,e₂ 1) = _
    rw [map_one]
  have hright (k : K) : e (inclusion le_sup_right (eS k)) = (1,eK k) := by
    have hh : eP (1,eS k) = inclusion le_sup_right (eS k) := by
      apply Subtype.ext
      simpa only [coe_one,one_mul,coe_inclusion] using hP 1 (eS k)
    change (eK.prodCongr e₂) (eP.symm (inclusion le_sup_right (eS k))) = _
    rw [←hh,eP.symm_apply_apply]
    change (eK 1,eK (eS.symm (eS k))) = _
    rw [map_one,eS.symm_apply_apply]
  have hZ : center J = ⊥ := by
    apply bot_unique
    intro z hz
    have hez := ((centerCongr e) ⟨z,hz⟩).property
    change e z ∈ center (Matrix.PSL3Two.SL × Matrix.PSL3Two.SL) at hez
    rw [Subgroup.center_prod,Matrix.PSL3Two.center_eq_bot,bot_prod_bot] at hez
    exact e.injective ((mem_bot.mp hez).trans e.map_one.symm)
  let hn : I ≤ normalizer (J : Set G) := sup_le J.le_normalizer hTN
  refine ⟨e,hleft,hright,hn,?_,?_⟩
  · exact (MulAut.congr e).injective.comp
      (join_normalizer_action_injective_of_pCore_eq_bot (T : Subgroup G) J T.isPGroup' hTN hZ hcore)
  · intro j
    apply MulEquiv.ext
    intro z
    change e ((j : J) * e.symm z * (j : J)⁻¹) = e j * z * (e j)⁻¹
    simp only [map_mul,map_inv,e.apply_symm_apply]

end CFSG.Quasithin.Chapter2.DoubleA3.Noncentrality