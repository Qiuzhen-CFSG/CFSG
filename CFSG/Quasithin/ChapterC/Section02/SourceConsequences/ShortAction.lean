module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.PerfectAction
public import Theory.GroupTheory.SylowKernelCore
import Mathlib.Tactic
/-!
# Perfect actors on the actual chi-block family

A normal characteristic-two subgroup of three-rank at most two has at most
two actual chi-blocks. Conjugation by an ambient perfect subgroup therefore
fixes each one. Applying the proved perfect-actor case of C.1.10 inside its
literal normalizer removes the ambient normality requirement and kills
an action trivial on the core quotient.

Source: Aschbacher–Smith, C.1.10 and the block step of C.2.12, pp.124,148.
-/
public section
namespace CFSG.Quasithin.ChapterC.SourceShortAction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A perfect actor fixes every chi-block in a normal characteristic-two
subgroup of three-rank at most two. The entire actual block family is used. -/
theorem perfect_normalizes_chi (X B : Subgroup G) [X.Normal] [Group.IsPerfect B]
    (hf : generalizedFitting X = pCore 2 X) (hr : primeRank 3 X ≤ 2)
    (K : Subgroup X) (hK : IsChiBlockIn K) :
    B ≤ normalizer (K.map X.subtype : Set G) := by
  classical
  let I := {Y : Subgroup X // IsChiBlockIn Y}
  let f : I → Subgroup G := fun i => i.val.map X.subtype
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact map_injective X.subtype_injective he
  have hsub : (Set.range fun g : G => (K.map X.subtype).map (MulAut.conj g).toMonoidHom) ⊆
      Set.range f := by
    rintro _ ⟨g,rfl⟩
    let e : X ≃* X := MulAut.conjNormal g
    refine ⟨⟨K.map e.toMonoidHom,RankOne.ChiProduct.chi_map_equiv e hK⟩,?_⟩
    change (K.map e.toMonoidHom).map X.subtype =
      (K.map X.subtype).map (MulAut.conj g).toMonoidHom
    rw [map_map,map_map]
    rfl
  have hi : (normalizer (K.map X.subtype : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans
      ((Set.ncard_range_of_injective hinj).le.trans
        (RankOne.ChiProduct.card_chiBlocks_le_two hf hr))
  exact le_of_isPerfect_of_index_le_two B _ hi

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The proved perfect-actor case of C.1.10 applies inside the actual
normalizer, so ambient normality of the short group is unnecessary. -/
theorem perfect_centralizes_short_of_normalizes (K B : Subgroup G) [Group.IsPerfect B]
    (hK : IsShort K) (hBK : B ≤ normalizer (K : Set G))
    (hc : ⁅K,B⁆ ≤ K.pCoreIn 2) : ⁅K,B⁆ = ⊥ := by
  let N := normalizer (K : Set G)
  let K' := K.subgroupOf N
  let B' := B.subgroupOf N
  let : K'.Normal := (normal_subgroupOf_iff_le_normalizer K.le_normalizer).mpr le_rfl
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hBK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBK).symm.surjective
  have hk : IsShort K' := RankOne.Solvable.isShort_of_equiv
    (subgroupOfEquivOfLe K.le_normalizer).symm hK
  have hc' : ⁅K',B'⁆ ≤ K'.pCoreIn 2 := by
    apply (map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_pCoreIn_of_injective 2 K' N.subtype N.subtype_injective,
      map_subgroupOf_eq_of_le K.le_normalizer,map_subgroupOf_eq_of_le hBK]
    exact hc
  have he := congrArg (map N.subtype)
    (BlockCommutation.perfect_actor_centralizes K' B' hk perfect_twoPerfect hc')
  rw [map_commutator] at he
  have hkmap : K'.map N.subtype = K := map_subgroupOf_eq_of_le K.le_normalizer
  have hbmap : B'.map N.subtype = B := map_subgroupOf_eq_of_le hBK
  rw [hkmap,hbmap] at he
  simpa only [map_subgroupOf_eq_of_le K.le_normalizer,
    map_subgroupOf_eq_of_le hBK,Subgroup.map_bot] using he
end CFSG.Quasithin.ChapterC.SourceShortAction
