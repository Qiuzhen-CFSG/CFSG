module
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualCommutator
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom

/-!
# Two-perfect normal images in a binary parabolic

A nontrivial two-perfect subgroup of the inner automorphisms of a standard
parabolic, normalized by its residual, is the inner image of that residual.
Two-perfectness first puts it inside the actual A₄. The normal-subgroup
classification of A₄ then excludes the identity and Klein four cases.

The original-group application uses this to recover L₁ from the action of
O²(Y ∩ N_G(L)), without discarding the kernel of the ambient quotient action.
Source: Aschbacher–Smith, assertion (!!) in 14.5.20, printed p.1019,
and 14.7.9, printed p.1045, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two.MarkedAutomorphisms

private theorem alternating_four_normal_twoPerfect
    {D : Type*} [Group D] (e : D ≃* alternatingGroup (Fin 4))
    (N : Subgroup D) [N.Normal] (hp : IsPPerfect 2 N) (hne : N ≠ ⊥) : N = ⊤ := by
  let B := N.map e.toMonoidHom
  let : B.Normal := Normal.map inferInstance _ e.surjective
  have hpB := hp.of_surjective (e.toMonoidHom.subgroupMap N)
    (e.toMonoidHom.subgroupMap_surjective N)
  have hneB : B ≠ ⊥ := fun h => hne ((N.map_eq_bot_iff_of_injective e.injective).mp h)
  have hB : B = ⊤ := by
    rcases AlternatingFourPair.normalA4 B with hz | hk | ht
    · exact (hneB hz).elim
    · have hpg : IsPGroup 2 B := by
        rw [hk]
        exact IsPGroup.of_card (n := 2)
          (alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num))
      have hh := hpB.hom_eq_one_of_isPGroup hpg (MonoidHom.id B)
      exact (hneB (eq_bot_iff.mpr (fun b hb => mem_bot.mpr
        (congrArg Subtype.val (DFunLike.congr_fun hh ⟨b,hb⟩))))).elim
    · exact ht
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr e.surjective]
  exact hB

/-- A nontrivial two-perfect group of parabolic automorphisms normalized
by the residual is precisely its inner A₄. -/
theorem twoPerfect_normalized_parabolic_image
    (P : Subgroup SL) (hP : P = pointParabolicSL ∨ P = lineParabolicSL)
    (X : Subgroup (MulAut SL)) (hp : IsPPerfect 2 X) (hne : X ≠ ⊥)
    (hXP : X ≤ P.map MulAut.conj)
    (hn : (residual P).map MulAut.conj ≤ normalizer (X : Set (MulAut SL))) :
    X = (residual P).map MulAut.conj := by
  let Q := P.map MulAut.conj
  let A := (residual P).map MulAut.conj
  have hXQ : IsPPerfect 2 (X.subgroupOf Q) := hp.of_surjective
    (subgroupOfEquivOfLe hXP).symm.toMonoidHom (subgroupOfEquivOfLe hXP).symm.surjective
  have hXA : X ≤ A := by
    have hh := map_mono (f := Q.subtype)
      (le_pResidual_of_isPPerfect (X.subgroupOf Q) hXQ)
    rw [map_subgroupOf_eq_of_le hXP] at hh
    have he := map_embedded_pResidual 2 P MulAut.conj
    exact hh.trans_eq he.symm
  let N := X.subgroupOf A
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have heP : Nonempty (residual P ≃* alternatingGroup (Fin 4)) := by
    rcases hP with rfl | rfl
    · exact ⟨pointResidualEquivAlternating⟩
    · exact ⟨lineResidualEquivAlternating⟩
  let eP := heP.some
  let eA : A ≃* alternatingGroup (Fin 4) :=
    (equivMapOfInjective (residual P) MulAut.conj conj_injective).symm.trans eP
  have hpN : IsPPerfect 2 N := hp.of_surjective
    (subgroupOfEquivOfLe hXA).symm.toMonoidHom (subgroupOfEquivOfLe hXA).symm.surjective
  have hneN : N ≠ ⊥ := by
    intro hh
    have hm := congrArg (Subgroup.map A.subtype) hh
    rw [map_subgroupOf_eq_of_le hXA, Subgroup.map_bot] at hm
    exact hne hm
  exact le_antisymm hXA (subgroupOf_eq_top.mp
    (alternating_four_normal_twoPerfect eA N hpN hneN))

end Matrix.PSL3Two.MarkedAutomorphisms
