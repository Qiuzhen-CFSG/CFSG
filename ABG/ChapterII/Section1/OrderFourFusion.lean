module
public import ABG.ChapterII.Section1.OrderFourQuaternion
public import ABG.ChapterII.Section1.SmallNormalizerFusionControl
public import ABG.ChapterII.Section1.QuaternionNormalizerFusion
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Global order-four fusion for a quasi-dihedral Sylow subgroup

For the exact quasi-dihedral fusion frame with chosen four subgroup `T` and
quaternion subgroup `Q`, outer automizer index six at `Q` gives exactly one
ambient conjugacy class of elements of order four; index two gives exactly
two. The denominator is the actual `Q C_G(Q)`. No restriction on the four
subgroup's automizer is required for these order-four conclusions.

At index two, apply the representative fusion relation to the relation
saying that an order-four first element is Sylow-conjugate to the second.
The four subgroup has no elements of order four, and the quaternion
normalizer introduces no new fusion. Hence the two Sylow classes stay
distinct. At index six, the normalizer realizes every quaternion
automorphism, which acts transitively on order-four elements. Every Sylow
order-four element has a conjugate in this chosen quaternion subgroup, so
the two Sylow classes merge. Finally, conjugating prime-power-order elements
into the chosen Sylow subgroup supplies global coverage in both cases.

This proves the order-four class-count clauses of all four alternatives in
ABG Chapter II §1 Proposition 1, article pp.10–11 of
`refs/latex/alperin-brauer-gorenstein.tex`. The returned class counts retain
actual representatives, coverage, and pairwise inequivalence.
-/

namespace ABG
variable {G : Type*} [Group G] [Finite G]
private theorem isConj_orderOf_eq {H : Type*} [Group H] {x y : H}
    (h : IsConj x y) : orderOf x = orderOf y := by
  obtain ⟨g, hg⟩ := h
  exact SemiconjBy.orderOf_eq (g : H) hg

private theorem order_four_fusion_control
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q)
    (hQ : outerAutomizerIndex Q = 2) {x y : P}
    (hx : orderOf x = 4) (hxy : IsConj (x : G) (y : G)) : IsConj x y := by
  have hrel : orderOf x = 4 → IsConj x y := by
    apply quasiDihedral_representative_fusion_relation P T Q hframe
      (fun x y : P => orderOf x = 4 → IsConj x y)
    · intro x _
      exact IsConj.refl _
    · intro x y z hxy hyz hx
      have hc := hxy hx
      exact hc.trans (hyz ((isConj_orderOf_eq hc).symm.trans hx))
    · intro x y hxy _
      exact hxy
    · intro g hg x y hxT hxy hx4
      have hpow : (⟨(x : G), hxT⟩ : T)^2 = 1 := by
        simpa only [hframe.2.2.2.1.exponent_two] using
          Monoid.pow_exponent_eq_one (⟨(x : G), hxT⟩ : T)
      have hpowP : x^2 = 1 := Subtype.ext (congrArg (fun z : T => (z : G)) hpow)
      have hd := orderOf_dvd_of_pow_eq_one hpowP
      rw [hx4] at hd
      norm_num at hd
    · intro g hg x y hxQ hxy _
      exact QuasiDihedral.small_normalizer_fusion_control (P : Subgroup G) Q
        hframe.1 hframe.2.2.1 (Or.inr hframe.2.2.2.2) hQ g hg x y hxQ hxy
    · exact hxy
  exact hrel hx

private theorem quaternion_order_four_isConj
    (Q : Subgroup G) (hQ : IsQuaternionGroup Q) (hi : outerAutomizerIndex Q = 6)
    (x y : Q) (hx : orderOf x = 4) (hy : orderOf y = 4) :
    IsConj (x : G) (y : G) := by
  obtain ⟨eQ⟩ := hQ
  have hsurj : Function.Surjective Q.normalizerMonoidHom := by
    apply Subgroup.normalizerMonoidHom_surjective_of_outer_index Q
    rw [QuaternionGroup.index_range_conj_of_equiv eQ]
    exact hi
  obtain ⟨f, hf⟩ := QuaternionGroup.exists_mulAut_eq_of_orderOf_eq_four
    (eQ x) (eQ y) ((eQ.orderOf_eq x).trans hx) ((eQ.orderOf_eq y).trans hy)
  let e := MulAut.congr eQ.symm f
  have he : e x = y := by
    change eQ.symm (f (eQ x)) = y
    rw [hf, MulEquiv.symm_apply_apply]
  obtain ⟨g, hg⟩ := hsurj e
  apply isConj_iff.mpr
  refine ⟨(g : G), ?_⟩
  have hh := congrArg (fun a : MulAut Q => ((a x) : G)) hg
  change (g : G) * (x : G) * (g : G)⁻¹ = (e x : G) at hh
  simpa only [he] using hh
/-- Quaternion outer automizer indices six and two give respectively one and two
ambient conjugacy classes of elements of order four. -/
public theorem quasiDihedral_order_four_fusion
    (P : Sylow 2 G) (T Q : Subgroup G) (hframe : QuasiDihedralFusionFrame P T Q) :
    (outerAutomizerIndex Q = 6 → HasElementConjugacyClassCount G 4 1) ∧
    (outerAutomizerIndex Q = 2 → HasElementConjugacyClassCount G 4 2) := by
  have hbridge : ∀ x : P, orderOf x = 4 → ∃ y : Q, IsConj (x : G) (y : G) := by
    intro x hx
    let e := Subgroup.subgroupOfEquivOfLe hframe.2.2.1
    obtain ⟨eQ⟩ := hframe.2.2.2.2
    obtain ⟨y, hy⟩ := QuasiDihedral.order_four_conjugate_into_quaternion hframe.1
      (Q.subgroupOf (P : Subgroup G)) ⟨e.trans eQ⟩ x hx
    exact ⟨e y, (P : Subgroup G).subtype.map_isConj hy⟩
  obtain ⟨x, y, hx, hy, hxy, hclasses⟩ := QuasiDihedral.order_four_conjugacy_classes hframe.1
  have intoP (z : G) (hz : orderOf z = 4) :
      ∃ u : P, IsConj z (u : G) ∧ orderOf u = 4 := by
    obtain ⟨u, hu⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 2) (by simpa using hz)
    refine ⟨u, hu, ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact (isConj_orderOf_eq hu).symm.trans hz
  constructor
  · intro hi
    have hconj (u v : P) (hu : orderOf u = 4) (hv : orderOf v = 4) :
        IsConj (u : G) (v : G) := by
      obtain ⟨uq, huq⟩ := hbridge u hu
      obtain ⟨vq, hvq⟩ := hbridge v hv
      have huq4 : orderOf uq = 4 := by
        rw [← Subgroup.orderOf_coe]
        exact (isConj_orderOf_eq huq).symm.trans ((Subgroup.orderOf_coe u).trans hu)
      have hvq4 : orderOf vq = 4 := by
        rw [← Subgroup.orderOf_coe]
        exact (isConj_orderOf_eq hvq).symm.trans ((Subgroup.orderOf_coe v).trans hv)
      exact huq.trans ((quaternion_order_four_isConj Q hframe.2.2.2.2 hi uq vq huq4 hvq4).trans hvq.symm)
    refine ⟨fun _ => (x : G), fun _ => (Subgroup.orderOf_coe x).trans hx, ?_, ?_⟩
    · intro i j _
      exact Subsingleton.elim _ _
    · intro z hz
      obtain ⟨u, hu, hu4⟩ := intoP z hz
      exact ⟨0, hu.trans (hconj u x hu4 hx)⟩
  · intro hi
    have hxyG : ¬ IsConj (x : G) (y : G) := fun h =>
      hxy (order_four_fusion_control P T Q hframe hi hx h)
    refine ⟨fun i : Fin 2 => if i = 0 then (x : G) else (y : G), ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using (Subgroup.orderOf_coe x).trans hx
      · simpa using (Subgroup.orderOf_coe y).trans hy
    · intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (hxyG (by simpa using hij))
      · exact False.elim (hxyG (by simpa using hij.symm))
      · rfl
    · intro z hz
      obtain ⟨u, hu, hu4⟩ := intoP z hz
      rcases hclasses u hu4 with hux | huy
      · refine ⟨0, ?_⟩
        simpa using hu.trans ((P : Subgroup G).subtype.map_isConj hux)
      · refine ⟨1, ?_⟩
        simpa using hu.trans ((P : Subgroup G).subtype.map_isConj huy)
end ABG
