module
public import GorensteinWalter.IndexTwoPSL2Core
public import Theory.GroupTheory.PGroup.TrivialImage

/-!
# Odd-index linear envelopes of a prescribed PSL2 core

In the odd-core-free dihedral index-two setting, an actual normal PSL2(F)
core determines the field order of the normal odd-index linear subgroup
supplied by Gorenstein--Walter. The result records a PSL2 or PGL2 model
over a finite odd field of the same order, including order three.

The two-group alternative contradicts the core's no-index-two property.
The A7 alternative contradicts the ambient normal index-two subgroup.
In either linear alternative the existing normal-core uniqueness theorem
identifies the field order; for PGL2 use its characteristic derived PSL2
subgroup, with the separate A4/S4 calculation already proved at order three.
This is the Proposition2 input to ABG II.3 Lemma2 (article pp22,24), without
an extra automorphism-surjectivity or outer-abelian hypothesis.
-/

namespace GorensteinWalter
universe u

public theorem exists_normal_linear_odd_index_of_psl2_core
    {H : Type u} [Group H] [Finite H]
    (hHd : HasDihedralSylowTwo H) (hO : pPrimeCore 2 H = ⊥)
    (K : Subgroup H) [K.Normal] (hKi : K.index = 2)
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (L : Subgroup H) [L.Normal] (eL : L ≃* PSL2 F) :
    ∃ (E : Type u) (iE : Field E) (_ : Finite E),
      let : Field E := iE
      IsOddPrimePower (Nat.card E) ∧ Nat.card E = Nat.card F ∧
        ∃ N : Subgroup H, N.Normal ∧ Odd N.index ∧
          (Nonempty (N ≃* PSL2 E) ∨ Nonempty (N ≃* PGL2 E)) := by
  let qE : (H ⧸ pPrimeCore 2 H) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (G := H) hO).trans
      (QuotientGroup.quotientBot (G := H))
  rcases gorensteinWalter H hHd with ⟨_, htwo⟩ | ⟨_, ⟨eA⟩⟩ |
      ⟨_, E, hE, Nq, hNq, hNi, hNm⟩
  · have hHtwo : IsPGroup 2 H := htwo.of_equiv qE
    have hLtwo := hHtwo.to_subgroup L
    have hno := no_normal_index_two_of_mulEquiv_psl2 F hF eL
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hLone : ∀ x : L, x = 1 :=
      MonoidHom.eq_one_of_no_normal_index_prime hno hLtwo (MonoidHom.id L)
    have hLc : Nat.card L = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (hLone a).trans (hLone b).symm⟩, ⟨1⟩⟩
    have hFc : Nat.card (PSL2 F) = 1 := (Nat.card_congr eL.toEquiv).symm.trans hLc
    have hF3 := odd_prime_power_three_le _ hF
    by_cases h3 : 3 < Nat.card F
    · have hc := psl2_card_ge_sixty_of_card_gt_three F hF h3
      omega
    · have hcard : Nat.card F = 3 := by omega
      rw [psl2_card_formula F hF, hcard] at hFc
      norm_num at hFc
  · let eH := qE.symm.trans eA
    let : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    let : IsSimpleGroup H := eH.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K inferInstance with hbot | htop
    · have hcard : Nat.card H = 2520 := by
        rw [Nat.card_congr eH.toEquiv, nat_card_alternatingGroup]
        norm_num
      rw [hbot, Subgroup.index_bot, hcard] at hKi
      contradiction
    · rw [htop, Subgroup.index_top] at hKi
      contradiction
  · let N := Nq.map qE.toMonoidHom
    let eN : Nq ≃* N := Subgroup.equivMapOfInjective Nq qE.toMonoidHom qE.injective
    have hNN : N.Normal := hNq.map qE.toMonoidHom qE.surjective
    let : N.Normal := hNN
    have hNodd : Odd N.index := by
      change Odd (Nq.map (qE : (H ⧸ pPrimeCore 2 H) →* H)).index
      rwa [Subgroup.index_map_equiv]
    rcases hNm with hpsl | hpgl
    · let e := eN.symm.trans hpsl.some
      have heq := unique_normal_psl2_core hHd hO K inferInstance hKi
        F hF L inferInstance eL E hE N hNN e
      exact ⟨E, inferInstance, inferInstance, hE, heq.2, N, hNN, hNodd, Or.inl ⟨e⟩⟩
    · let e := eN.symm.trans hpgl.some
      let C : Subgroup H := (commutator N).map N.subtype
      have hCN : C.Normal := ConjAct.normal_of_characteristic_of_normal
      let eC : C ≃* PSL2 E :=
        (Subgroup.equivMapOfInjective _ N.subtype N.subtype_injective).symm.trans
          (commutator_mulEquiv_psl2_of_mulEquiv_pgl2 E hE e).some
      have heq := unique_normal_psl2_core hHd hO K inferInstance hKi
        F hF L inferInstance eL E hE C hCN eC
      exact ⟨E, inferInstance, inferInstance, hE, heq.2, N, hNN, hNodd, Or.inr ⟨e⟩⟩

end GorensteinWalter
