module

public import Theory.GroupTheory.GeneralizedFitting.ComponentSylowCore
public import Theory.GroupTheory.PGroup.IndexTwoElementaryConjugate
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Elementary actors exchanging a component pair

If the component normalizer has index two, a moving actor generates the
full component residual orbit. If its component stabilizer centralizes
the component, elementary commutation makes that stabilizer centralize
the whole orbit. The ambient two-core is its only possible kernel. With
trivial two-core, the actor embeds in the two-element permutation quotient
and has rank exactly one.

Source: Aschbacher–Smith, E.1.11, printed p.214, specialized to two factors.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem moved_pair_orbit_eq_residual (T : Sylow 2 G)
    {K A : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hlayer : pResidual 2 G = componentLayer G)
    (hindex : (normalizer (K : Set G)).index = 2)
    (hm : ¬ A ≤ normalizer (K : Set G)) :
    componentOrbit K A = pResidual 2 G := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hm
  let D := K.map (MulAut.conj a).toMonoidHom
  let N := K ⊔ D
  let : N.Normal := sup_conjugate_normal_of_normalizer_index_two K hindex a han
  have hNT : N ⊔ (T : Subgroup G) = ⊤ := top_unique (by
    rw [← hgen]; exact sup_le_sup le_sup_left le_rfl)
  apply le_antisymm
  · rw [hlayer]
    exact iSup_le fun b => le_sSup (hK.map_conj b)
  · apply le_trans (show pResidual 2 G ≤ N from sInf_le
      ⟨inferInstance,isPGroup_quotient_of_sup_eq_top N (T : Subgroup G) T.isPGroup' hNT⟩)
    exact sup_le (le_componentOrbit K A)
      (le_iSup (fun b : A => K.map (MulAut.conj (b:G)).toMonoidHom) ⟨a,ha⟩)

theorem rank_one_of_moved_pair_and_fixed_stabilizer
    (T : Sylow 2 G) {K A : Subgroup G} (hK : IsComponent G K)
    (hgen : K ⊔ (T : Subgroup G) = ⊤)
    (hlayer : pResidual 2 G = componentLayer G)
    (hcore : pCore 2 G = ⊥)
    (hindex : (normalizer (K : Set G)).index = 2)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G))
    (hm : ¬ A ≤ normalizer (K : Set G))
    (hfix : A ⊓ normalizer (K : Set G) ≤ centralizer (K : Set G)) :
    Group.rank A = 1 := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  let V := A ⊓ normalizer (K : Set G)
  have hAV : A ≤ centralizer (V : Set G) := by
    intro a ha v hv
    exact congrArg Subtype.val (mul_comm (⟨v,hv.1⟩ : A) (⟨a,ha⟩ : A))
  have hEC : componentOrbit K A ≤ centralizer (V : Set G) :=
    iSup_conjugates_le_of_le_normalizer K A (centralizer (V : Set G))
      (le_centralizer_iff.mp hfix)
      (hAV.trans (centralizer (V : Set G)).le_normalizer)
  have hTmove : ¬ (T : Subgroup G) ≤ normalizer (K : Set G) := fun h => hm (hAT.trans h)
  have he : componentOrbit K (T : Subgroup G) = componentOrbit K A :=
    (moved_pair_orbit_eq_residual T hK hgen hlayer hindex hTmove).trans
      (moved_pair_orbit_eq_residual T hK hgen hlayer hindex hm).symm
  have hvb : V = ⊥ := by
    apply le_bot_iff.mp
    rw [← hcore, ← hK.sylow_centralizer_orbit_eq_pCore T hgen, he]
    exact le_inf (inf_le_left.trans hAT) (le_centralizer_iff.mp hEC)
  have hc : Nat.card A ≤ 2 := by
    let N := normalizer (K : Set G)
    let : N.Normal := normal_of_index_eq_two hindex
    have hd := relIndex_dvd_index_of_normal (H := N) (K := A)
    rw [hindex, ← inf_relIndex_left A N, show A ⊓ N = ⊥ from hvb, relIndex_bot_left] at hd
    exact Nat.le_of_dvd (by decide) hd
  have hb : A ≠ ⊥ := fun he => hm (he ▸ bot_le)
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hb
  exact Nat.le_antisymm (IsElementaryAbelian.rank_le_of_card_le A (by simpa using hc))
    (Group.rank_pos A)

end Theory.GroupTheory
