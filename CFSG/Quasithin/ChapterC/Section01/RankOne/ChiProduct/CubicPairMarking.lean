module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.CubicOrbit
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms

/-!
# Marking both original factors of a two-block orbit

When the Sylow orbit of an A₃ block has order 144, it is the join of
the original block and a distinct Sylow conjugate. C.1.9 makes the factors
commute, and their trivial centers make them disjoint. The multiplication
isomorphism supplies an A₄² marking taking the original two factors to
the literal coordinate axes. In particular the original Sylow action
interchanges these axes; this property is not inferred from an abstract
unmarked A₄² model.

Source: Aschbacher--Smith C.1.28 and 14.1.10, printed pp.133--134,978.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

/-- The literal two-axis marking retains the original block and a Sylow conjugate. -/
theorem cubic_pair_marking
    (hf : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (S : Sylow 2 G) (X : Subgroup G) (hb : IsBlock X) (ha : IsAlternatingBlock X 3)
    (hcard : Nat.card (conjugateSpanBy X (S : Subgroup G)) = 144) :
    let N := conjugateSpanBy X (S : Subgroup G)
    ∃ t : S, X.map (MulAut.conj (t : G)).toMonoidHom ≠ X ∧
      ∃ e : N ≃* AlternatingFourPair.Model,
        (X.subgroupOf N).map e.toMonoidHom = AlternatingFourPair.axis0 ∧
        ((X.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf N).map e.toMonoidHom =
          AlternatingFourPair.axis1 := by
  classical
  let N := conjugateSpanBy X (S : Subgroup G)
  have hchi : IsChiBlockIn X := ⟨hb,Or.inr ⟨3,by decide,ha⟩⟩
  obtain ⟨aX⟩ := ha.equiv_alternatingFour
  have hXcard : Nat.card X = 12 := (Nat.card_congr aX.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by norm_num))
  have hm : ∃ t : S, X.map (MulAut.conj (t : G)).toMonoidHom ≠ X := by
    by_contra hn
    push Not at hn
    have hNX : N = X := by
      apply le_antisymm ?_ (le_conjugateSpanBy X _)
      rw [conjugateSpanBy_eq_iSup_conj]
      exact iSup_le fun t => (hn t).le
    change Nat.card N = 144 at hcard
    rw [hNX,hXcard] at hcard
    norm_num at hcard
  obtain ⟨t,ht⟩ := hm
  let Y := X.map (MulAut.conj (t : G)).toMonoidHom
  have hYchi := chi_map_equiv (MulAut.conj (t : G)) hchi
  have hYa := Solvable.isAlternatingBlock_of_equiv ((MulAut.conj (t : G)).subgroupMap X) ha
  obtain ⟨aY0⟩ := hYa.equiv_alternatingFour
  let aY : Y ≃* AlternatingFourPair.A := aY0
  have hpair : ({X,Y} : Set (Subgroup G)) = {K | IsChiBlockIn K} := by
    apply Set.eq_of_subset_of_ncard_le
    · intro K hK
      rcases Set.mem_insert_iff.mp hK with rfl | hK
      · exact hchi
      · exact Set.mem_singleton_iff.mp hK ▸ hYchi
    · rw [Set.ncard_pair ht.symm]
      exact card_chiBlocks_le_two hf hr
    · exact Set.toFinite _
  have hNXY : N = X ⊔ Y := by
    apply le_antisymm
    · rw [show N = conjugateSpanBy X (S : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro s
      have hh : X.map (MulAut.conj (s : G)).toMonoidHom ∈ ({X,Y} : Set (Subgroup G)) := by
        rw [hpair]
        exact chi_map_equiv (MulAut.conj (s : G)) hchi
      rcases Set.mem_insert_iff.mp hh with he | he
      · rw [he]; exact le_sup_left
      · rw [Set.mem_singleton_iff.mp he]; exact le_sup_right
    · refine sup_le (le_conjugateSpanBy X _) ?_
      rw [show N = conjugateSpanBy X (S : Subgroup G) from rfl,conjugateSpanBy_eq_iSup_conj]
      exact le_iSup (fun s : S => X.map (MulAut.conj (s : G)).toMonoidHom) t
  have hc : X ≤ centralizer (Y : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (blocks_commute (blockCommutationHypothesis_of_fitting hf) hb hYchi.1 ht.symm)
  have hd : Disjoint X Y := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have hz : (⟨x,hx.1⟩ : X) ∈ center X :=
      mem_center_iff.mpr (fun y => Subtype.ext ((hc y.property x hx.2).symm))
    rw [ha.center_eq_bot,mem_bot] at hz
    exact congrArg Subtype.val hz
  obtain ⟨b,hbprod⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting X Y hd hc
  let d : X × Y ≃* N := b.trans (MulEquiv.subgroupCongr hNXY.symm)
  let e : N ≃* AlternatingFourPair.Model := d.symm.trans (aX.prodCongr aY)
  have hXN : X ≤ N := hNXY ▸ le_sup_left
  have hYN : Y ≤ N := hNXY ▸ le_sup_right
  have hdx (x : X) : d (x,1) = inclusion hXN x := by
    apply Subtype.ext
    exact (hbprod x 1).trans (mul_one (x : G))
  have hdy (y : Y) : d (1,y) = inclusion hYN y := by
    apply Subtype.ext
    exact (hbprod 1 y).trans (one_mul (y : G))
  have hex (x : X) : e (inclusion hXN x) = (aX x,1) := by
    rw [←hdx]
    change (aX.prodCongr aY) (d.symm (d (x,1))) = _
    rw [d.symm_apply_apply]
    change (aX x,aY 1) = _
    rw [map_one]
  have hey (y : Y) : e (inclusion hYN y) = (1,aY y) := by
    rw [←hdy]
    change (aX.prodCongr aY) (d.symm (d (1,y))) = _
    rw [d.symm_apply_apply]
    change (aX 1,aY y) = _
    rw [map_one]
  refine ⟨t,ht,e,?_,?_⟩
  · apply le_antisymm
    · rintro v ⟨x,hx,rfl⟩
      have he : x = inclusion hXN ⟨x,hx⟩ := rfl
      change e x ∈ AlternatingFourPair.axis0
      rw [he,hex]
      exact ⟨mem_top _,by simp⟩
    · intro v hv
      have hv2 : v.2 = 1 := hv.2
      refine ⟨inclusion hXN (aX.symm v.1),by exact (aX.symm v.1).property,?_⟩
      change e (inclusion hXN (aX.symm v.1)) = v
      rw [hex,aX.apply_symm_apply]
      exact Prod.ext rfl hv2.symm
  · apply le_antisymm
    · rintro v ⟨y,hy,rfl⟩
      have he : y = inclusion hYN ⟨y,hy⟩ := rfl
      change e y ∈ AlternatingFourPair.axis1
      rw [he,hey]
      exact ⟨by simp,mem_top _⟩
    · intro v hv
      have hv1 : v.1 = 1 := hv.1
      refine ⟨inclusion hYN (aY.symm v.2),by exact (aY.symm v.2).property,?_⟩
      change e (inclusion hYN (aY.symm v.2)) = v
      rw [hey,aY.apply_symm_apply]
      exact Prod.ext hv1.symm rfl

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
