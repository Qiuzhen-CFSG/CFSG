module
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.ThreeLocal.FusionSylow.InvolutionFusion

/-!
# The center and Sylow two-subgroups of the three-centralizer

Inside C_G(c), fusion of the involutions rules out central involutions. The
center embeds in the abelian involution centralizer of order twelve and
contains c, so its order is three. A Sylow two-subgroup contains a central
involution, hence embeds in an involution centralizer; its order is four.
The coordinate centralizer has exponent six, which rules out elements of
order four and proves that these Sylow subgroups are elementary abelian.

These are inputs to the centralizer argument in Janko's Lemma 8. They do not
identify C_G(c) or determine the Sylow three-subgroups of the ambient group.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 3, pp.7–8.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
open LocalModelDichotomy

local instance : DecidableEq TwistedModel := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) SemidirectProduct.ext_iff.symm

local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The intrinsic center of C_G(c) has order three. -/
public theorem three_centralizer_center_card
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z) :
    Nat.card (center (centralizer ({into D k c} : Set G))) = 3 := by
  let H := centralizer ({into D k c} : Set G)
  let zH : H := markedInvolutionInThreeCentralizer D k
  have hc1 : z 1 * c = c * z 1 := by decide +kernel
  let tH : H := ⟨into D k (z 1), mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg (into D k) hc1)⟩
  have hto : orderOf tH = 2 := by
    rw [orderOf_mk, orderOf_injective (into D k) (into_injective D k), z_order]
  have htz : tH ≠ zH := by
    intro hh
    have hh' : into D k (z 1) = into D k (z 0) :=
      (congrArg Subtype.val hh).trans (into_z_zero D k).symm
    have hz1 : z 1 ≠ z 0 := by decide +kernel
    exact hz1 (into_injective D k hh')
  have hzn : zH ∉ center H := by
    intro hz
    exact htz ((three_centralizer_involution_fusion D k h2 tH hto).eq_of_right_mem_center hz)
  have hodd : ¬2 ∣ Nat.card (center H) := by
    intro he
    obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := center H) 2 he
    have hh := three_centralizer_involution_fusion D k h2 (s : H)
      (by simpa only [orderOf_coe] using hs)
    apply hzn
    change markedInvolutionInThreeCentralizer D k ∈ center H
    rw [← hh.eq_of_left_mem_center s.property]
    exact s.property
  have hd := card_dvd_of_le (center_le_centralizer ({zH} : Set H))
  have hzcard : Nat.card (centralizer ({zH} : Set H)) = 12 :=
    marked_three_involution_centralizer_card D k
  rw [hzcard] at hd
  let cH : H := ⟨into D k c, mem_centralizer_singleton_iff.mpr rfl⟩
  have hcZ : cH ∈ center H := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
  have hco : orderOf (⟨cH, hcZ⟩ : center H) = 3 := by
    rw [orderOf_mk, orderOf_mk, orderOf_injective (into D k) (into_injective D k)]
    exact actor_orders.2.2.1
  have h3 : 3 ∣ Nat.card (center H) := hco ▸ orderOf_dvd_natCard (⟨cH, hcZ⟩ : center H)
  have hs : Nat.card (center H) ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hdiv] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  change Nat.card (center H) = 3
  omega

/-- Every Sylow two-subgroup of C_G(c) has order four. -/
public theorem three_centralizer_sylow_two_card
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (S : Sylow 2 (centralizer ({into D k c} : Set G))) : Nat.card S = 4 := by
  let H := centralizer ({into D k c} : Set G)
  have h4H : 4 ∣ Nat.card H := by
    have hd := (centralizer ({markedInvolutionInThreeCentralizer D k} : Set H)).card_subgroup_dvd_card
    rw [marked_three_involution_centralizer_card D k] at hd
    exact dvd_trans (by decide : 4 ∣ 12) hd
  have h4S : 4 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) h4H
  have hSnt : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 4) (Nat.le_of_dvd Nat.card_pos h4S))
  let := hSnt
  let := S.isPGroup'.center_nontrivial
  obtain ⟨n, hn, hcn⟩ := (S.isPGroup'.to_subgroup (center S)).nontrivial_iff_card.mp
    (inferInstance : Nontrivial (center S))
  have h2Z : 2 ∣ Nat.card (center S) := by
    rw [hcn]
    exact dvd_pow_self _ (Nat.ne_of_gt hn)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 h2Z
  have htH : orderOf ((t : S) : H) = 2 := by
    simpa only [orderOf_coe] using ht
  have hSC : (S : Subgroup H) ≤ centralizer ({((t : S) : H)} : Set H) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp t.property ⟨x, hx⟩))
  have hd := card_dvd_of_le hSC
  rw [(three_centralizer_involution_structure D k h2 ((t : S) : H) htH).1] at hd
  have hns : ¬3 ∣ Nat.card S := by
    obtain ⟨m, hm⟩ := S.isPGroup'.exists_card_eq
    rw [hm]
    intro h
    exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  have hs : Nat.card S ∈ Nat.divisors 12 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hdiv : Nat.divisors 12 = {1, 2, 3, 4, 6, 12} := by decide
  rw [hdiv] at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  omega

omit [Finite G] in
/-- An element commuting with an involution inside C_G(c) has sixth power one. -/
public theorem three_centralizer_pow_six_of_commuting_involution
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (x t : centralizer ({into D k c} : Set G)) (ht : orderOf t = 2)
    (hxt : Commute x t) : x ^ 6 = 1 := by
  let H := centralizer ({into D k c} : Set G)
  let zH : H := markedInvolutionInThreeCentralizer D k
  obtain ⟨g, hg⟩ := isConj_iff.mp (three_centralizer_involution_fusion D k h2 t ht)
  let f := MulAut.conj g
  have hgz : f t = zH := hg
  let y : centralizer ({zH} : Set H) := ⟨f x, mem_centralizer_singleton_iff.mpr (by
    rw [← hgz]
    simpa only [← map_mul] using congrArg f hxt.eq)⟩
  let e := markedThreeInvolutionCentralizerEquiv D k
  have hm : ∀ v : TwistedModel, v * c = c * v → v ^ 6 = 1 := by decide +kernel
  have hy : y ^ 6 = 1 := by
    apply e.symm.injective
    simp only [map_pow, map_one]
    exact Subtype.ext (hm (e.symm y)
      (mem_centralizer_singleton_iff.mp (e.symm y).property))
  have hy' := congrArg Subtype.val hy
  change (f x) ^ 6 = 1 at hy'
  apply f.injective
  simpa only [map_pow, map_one] using hy'

/-- C_G(c) has no elements of order four. -/
public theorem three_centralizer_no_order_four
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (x : centralizer ({into D k c} : Set G)) : orderOf x ≠ 4 := by
  intro hx
  have ht : orderOf (x ^ 2) = 2 := by rw [orderOf_pow, hx]; decide
  have hp := three_centralizer_pow_six_of_commuting_involution D k h2 x (x ^ 2) ht
    (Commute.refl x |>.pow_right 2)
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [hx] at hd
  norm_num at hd

/-- The Sylow two-subgroups of C_G(c) are four-groups. -/
public theorem three_centralizer_sylow_two_elementary
    (h2 : ∀ t : G, orderOf t = 2 → IsConj t D.z)
    (S : Sylow 2 (centralizer ({into D k c} : Set G))) : IsElementaryAbelian 2 S := by
  have ho (x : S) : orderOf x ∣ 2 := by
    have hd := orderOf_dvd_natCard x
    change orderOf x ∣ Nat.card (S : Subgroup (centralizer ({into D k c} : Set G))) at hd
    rw [three_centralizer_sylow_two_card D k h2 S] at hd
    have hn : orderOf x ≠ 4 := by
      simpa only [orderOf_coe] using three_centralizer_no_order_four D k h2 (x : _)
    have hs : orderOf x ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hdiv : Nat.divisors 4 = {1, 2, 4} := by decide
    rw [hdiv] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h
    · simp [h]
    · simp [h]
    · exact (hn h).elim
  exact {
    is_comm.comm := fun x y => (Commute.of_orderOf_dvd_two ho x y).eq
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => orderOf_dvd_iff_pow_eq_one.mp (ho x)) }

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII
