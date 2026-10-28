module
public import Theory.GroupAction.ElementaryNineFourSemidirect
public import Theory.GroupAction.FourGroupOddCenter
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.GroupAction.OddInvolutionFixedFaithful
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.ElementaryAbelian.Quotient

/-!
# Recognizing the normal-nine extension on an elementary sixteen

In a faithful binary action of degree four, an order-nine subgroup is
an elementary nine and has an odd centralizer. Thus an elementary four
complement acts faithfully on it. A nonidentity member of that four-group
fixes a nonidentity vector; its proper fixed subgroup is an invariant line.
The existing affine-action recognition then identifies the semidirect
product with the literal group S3 × S3.

The odd-centralizer proof is the dimension-four argument from the private
lemma in `ElementaryThirtyTwoNineNormalizer`, retained here so that the
public result does not change an existing module's boundary. Its proof
restricts an odd actor to an involution's fixed space and compares checked
binary automorphism orders.

Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 3.1,
printed pp.36–37. This proof identifies the given order-thirty-six subgroup
without assuming the order or structure of the full nine-subgroup normalizer.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace SixteenOddComplements

/-- Faithful four-group actions on a nine-group have an invariant line. -/
theorem invariant_three_of_four_action
    {E D : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    [Group D] [Finite D] [IsElementaryAbelian 2 D]
    (ρ : D →* MulAut E) (hρ : Function.Injective ρ)
    (hE : Nat.card E = 9) (hD : Nat.card D = 4) :
    ∃ L : Subgroup E, Nat.card L = 3 ∧ ∀ d : D, ∀ x ∈ L, ρ d x ∈ L := by
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by rw [hE]; decide)
  obtain ⟨t, ht, x, hx, htx⟩ :=
    Theory.GroupAction.exists_nontrivial_fixed_of_elementaryFour hD ρ
  let L := (ρ t).fixedSubgroup
  have hL1 : Nat.card L ≠ 1 := by
    intro hh
    exact hx (show x ∈ (⊥ : Subgroup E) from card_eq_one.mp hh ▸ (MulAut.mem_fixedSubgroup (ρ t) x).mpr htx)
  have hL9 : Nat.card L ≠ 9 := by
    intro hh
    have htop : L = ⊤ := L.eq_top_of_card_eq (hh.trans hE.symm)
    apply ht
    apply hρ
    rw [map_one]
    ext y
    exact (MulAut.mem_fixedSubgroup (ρ t) y).mp (show y ∈ L by rw [htop]; trivial)
  have hdiv : Nat.card L ∣ 3 ^ 2 := by simpa [hE] using L.card_subgroup_dvd_card
  obtain ⟨n, hn, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
  have hLc : Nat.card L = 3 := by
    interval_cases n
    · exact (hL1 hcard).elim
    · exact hcard
    · exact (hL9 hcard).elim
  refine ⟨L, hLc, ?_⟩
  intro d y hy
  apply (MulAut.mem_fixedSubgroup (ρ t) _).mpr
  have hy' := (MulAut.mem_fixedSubgroup (ρ t) y).mp hy
  have hc : ρ t * ρ d = ρ d * ρ t := by rw [← map_mul, ← map_mul, mul_comm t d]
  calc
    ρ t (ρ d y) = ρ d (ρ t y) := congrArg (fun f : MulAut E => f y) hc
    _ = ρ d y := congrArg (ρ d) hy'

private instance elementary_subgroup
    {E : Type*} [Group E] [IsElementaryAbelian 2 E] (D : Subgroup E) :
    IsElementaryAbelian 2 D where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom D.subtype D.subtype_injective).trans
    (IsElementaryAbelian.exponent_dvd_p 2 E)

/-- The nine-subgroup centralizer has odd order. The argument is the
four-dimensional layer of ElementaryThirtyTwoNineNormalizer. -/
theorem odd_centralizer_nine
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (A : Subgroup (MulAut V)) (hA : Nat.card A = 9) :
    Odd (Nat.card (centralizer (A : Set (MulAut V)))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let C := centralizer (A : Set (MulAut V))
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.mp heven)
  let t : MulAut V := c
  have ht : orderOf t = 2 := (orderOf_injective C.subtype C.subtype_injective c).trans hc
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  let Q := zpowers t
  have hQA : Q ≤ centralizer (A : Set (MulAut V)) := zpowers_le.mpr c.property
  have hAQ : A ≤ centralizer (Q : Set (MulAut V)) := le_centralizer_iff.mp hQA
  let F := FixedPoints.subgroup Q V
  let : IsInvariant A V F := fixedPoints_isInvariant_of_normalizing_actor A Q
    (hAQ.trans (centralizer_le_normalizer _))
  have hfaith := MulAut.odd_centralizer_fixed_action_faithful t ht2 A
    (by rw [hA]; decide) hAQ
  let f := MulDistribMulAction.toMulAut A F
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply hfaith.le
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact congrArg Subtype.val (MulEquiv.congr_fun (MonoidHom.mem_ker.mp ha) ⟨v, hv⟩)
  have hdiv : 9 ∣ Nat.card (MulAut F) := hA ▸ card_dvd_of_injective f hf
  have hproper : Nat.card F ≠ 16 := by
    intro hh
    have htop : F = ⊤ := F.eq_top_of_card_eq (hh.trans hV.symm)
    have htone : t = 1 := by
      apply MulEquiv.ext
      intro v
      have hv : v ∈ F := htop ▸ mem_top v
      exact hv ⟨t, mem_zpowers t⟩
    rw [htone, orderOf_one] at ht
    omega
  have hFdiv : Nat.card F ∣ 2 ^ 4 := by
    simpa [hV] using F.card_subgroup_dvd_card
  obtain ⟨n, hn, hncard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow F n hncard] at hdiv
  interval_cases n <;> norm_num [Fin.prod_univ_succ] at hdiv
  exact hproper hncard

/-- A normal nine with an elementary four complement in GL(V), for
binary V of order sixteen, gives the genuine symmetric-group product. -/
theorem equiv_of_normal_nine_four
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16) (H : Subgroup (MulAut V))
    (J : Subgroup H) [J.Normal] (hJ : Nat.card J = 9)
    (P : Subgroup H) [IsElementaryAbelian 2 P] (hP : Nat.card P = 4)
    (hcomp : J.IsComplement' P) :
    Nonempty (H ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let A := J.map H.subtype
  have hA : Nat.card A = 9 := (card_map_of_injective H.subtype_injective).trans hJ
  let : IsElementaryAbelian 3 A :=
    SmallNonabelianTwoGroup.elementaryAbelian_of_card_dvd_nine
      (IsElementaryAbelian.isPGroup 2 V) (by omega) A (hA ▸ dvd_rfl)
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let : IsElementaryAbelian 3 J :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let PP := P.map H.subtype
  have hPP : Nat.card PP = 4 := (card_map_of_injective H.subtype_injective).trans hP
  have hd : Disjoint PP (centralizer (A : Set (MulAut V))) :=
    disjoint_of_coprime_natCard (by
      rw [hPP]
      exact (odd_centralizer_nine hV A hA).coprime_two_left.pow_left 2)
  let f : P →* MulAut J := J.normalizerMonoidHom.comp
    (inclusion (J.normalizer_eq_top ▸ le_top))
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro p hp
    have hk : (inclusion (show P ≤ normalizer (J : Set H) by
        rw [J.normalizer_eq_top]; exact le_top) p) ∈ J.normalizerMonoidHom.ker := hp
    rw [normalizerMonoidHom_ker] at hk
    have hc : ((p : H) : MulAut V) ∈ centralizer (A : Set (MulAut V)) := by
      rintro b ⟨j, hj, rfl⟩
      exact congrArg Subtype.val (hk j hj)
    exact Subtype.ext (Subtype.ext (disjoint_def.mp hd
      (mem_map_of_mem H.subtype p.property) hc))
  obtain ⟨L, hL, hLi⟩ := invariant_three_of_four_action f hf hJ hP
  obtain ⟨eprod⟩ := ElementaryNineFourSemidirect.nonempty_mulEquiv f hJ hP hf L hL hLi
  exact ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm.trans eprod⟩

end SixteenOddComplements
end
