module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientFusion
public import Theory.GroupTheory.FourGroupCentralizerOddCore
public import Theory.GroupTheory.QuaternionCentralProductInvolutions

/-!
# Simplicity forced by the G₂(3) local configuration

An element outside H₁H₂ has square in the quaternion core: its two
permutation coordinates are odd permutations of three points. If an
ambient normal subgroup contains an involution, fusion puts all square-one
elements in it, including the generators of the quaternion core and the
outside complement. Its intersection with H has odd index dividing nine;
the outside-square calculation then puts all of H in that intersection.
The existing ambient Sylow normalizer control and Frattini argument force
the normal subgroup to be the whole group.

For an odd normal subgroup, its intersection with H commutes with the
quaternion core and is therefore trivial. The marked fused four-group
then acts without nonidentity fixed points, forcing the normal subgroup
itself to be trivial. Cauchy's theorem exhausts the two cases, proving
simplicity without adding it to the recognition hypotheses.

This removes the normal-subgroup obstruction in the ambient recognition
of Aschbacher–Smith I.4.5, printed p.417, using the fusion conclusion of
Fong–Wong §2F(ii), Nagoya Math. J.36 (1969), pp.153–154. It does not yet
identify the group with the octonion model. Chapter14Simplicity applies
the result to the original source-local configuration.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal

theorem outside_square_mem_core (h : c.H) (hout : h ∉ c.H₁ ⊔ c.H₂) :
    h ^ 2 ∈ quaternionCore c := by
  rw [← coreOuterAction_kernel c]
  change coreOuterAction c (h ^ 2) = 1
  rw [map_pow]
  have haxis (i : BinaryFourPlus.C2) : (coreOuterAction c h).left i ^ 2 = 1 := by
    apply (by decide : ∀ s : Equiv.Perm (Fin 3), Equiv.Perm.sign s ≠ 1 → s ^ 2 = 1)
    intro hh
    apply hout
    rw [← axisSign_kernel c i]
    exact hh
  have hr := coreOuterAction_preserves_factors c h
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_two, hr] using haxis i
  · simp [pow_two, hr]

include c in
private theorem square_one_mem_normal (N : Subgroup G) [N.Normal]
    (z : G) (hz : orderOf z = 2) (hzN : z ∈ N) (x : G) (hx : x ^ 2 = 1) : x ∈ N := by
  by_cases he : x = 1
  · simp [he]
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_conjugate c z x hz (orderOf_eq_prime hx he))
  exact hg ▸ (inferInstance : N.Normal).conj_mem z hzN g

theorem core_le_normal_of_involution (N : Subgroup G) [N.Normal]
    (z : G) (hz : orderOf z = 2) (hzN : z ∈ N) :
    (quaternionCore c).map c.H.subtype ≤ N := by
  let d := quaternionCoreData c
  have hh := quaternion_central_product_involutions_generate d.left d.right
    d.left_model d.right_model d.intersection_card d.commute
  rw [d.span] at hh
  have htop : (⊤ : Subgroup (quaternionCore c)) ≤
      N.comap (c.H.subtype.comp (quaternionCore c).subtype) := by
    rw [← hh]
    apply (closure_le _).mpr
    intro x hx
    apply square_one_mem_normal c N z hz hzN
    exact (congrArg (c.H.subtype.comp (quaternionCore c).subtype) hx.2).trans
      (map_one _)
  rintro x ⟨q, hq, rfl⟩
  exact htop (mem_top (⟨q,hq⟩ : quaternionCore c))

theorem H_le_normal_of_involution (N : Subgroup G) [N.Normal]
    (z : G) (hz : orderOf z = 2) (hzN : z ∈ N) : c.H ≤ N := by
  classical
  let Q := quaternionCore c
  let D := N.subgroupOf c.H
  have hQD : Q ≤ D := fun q hq => core_le_normal_of_involution c N z hz hzN
    (mem_map_of_mem c.H.subtype hq)
  obtain ⟨_,n,_,_,hn,hout,_,_⟩ := exists_fused_involution_complement c
  have hnD : n ∈ D := square_one_mem_normal c N z hz hzN n
    (congrArg c.H.subtype (hn ▸ pow_orderOf_eq_one n))
  have hnQ : n ∉ Q := fun hh => hout
    ((sup_le_sup (c.H₁.pCoreIn_le 2) (c.H₂.pCoreIn_le 2)) hh)
  have hdis : Q ⊓ zpowers n = ⊥ := by
    apply eq_bot_iff.mpr
    rintro x ⟨hxQ,hxn⟩
    change x = 1
    change x ∈ Q at hxQ
    change x ∈ zpowers n at hxn
    rw [mem_zpowers_iff_mem_range_orderOf,hn] at hxn
    obtain ⟨i,hi,he⟩ := Finset.mem_image.mp hxn
    have hi2 := Finset.mem_range.mp hi
    interval_cases i
    · simpa using he.symm
    · exact (hnQ (by simpa only [←he,pow_one] using hxQ)).elim
  have hP : Nat.card (Q ⊔ zpowers n : Subgroup c.H) = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes Q (zpowers n)
      (show zpowers n ≤ normalizer (Q : Set c.H) from le_normalizer_of_normal)
    rw [hdis,Nat.card_zpowers,hn,quaternionCore_card c] at hh
    simpa using hh.symm
  have hPi : (Q ⊔ zpowers n : Subgroup c.H).index = 9 := by
    have hh := (Q ⊔ zpowers n : Subgroup c.H).card_mul_index
    rw [hP,H_card c] at hh
    omega
  have hDi : D.index ∣ 9 := hPi ▸ index_dvd_of_le (sup_le hQD (zpowers_le.mpr hnD))
  have hcop : Nat.Coprime 2 (Nat.card (c.H ⧸ D)) :=
    (by decide : Nat.Coprime 2 9).of_dvd_right hDi
  have outside (h : c.H) (hh : h ∉ c.H₁ ⊔ c.H₂) : h ∈ D := by
    apply (QuotientGroup.eq_one_iff h).mp
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hcop
    · apply orderOf_dvd_of_pow_eq_one
      change (QuotientGroup.mk' D h) ^ 2 = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (h ^ 2)).mpr (hQD (outside_square_mem_core c h hh))
    · exact orderOf_dvd_natCard _
  intro x hx
  let h : c.H := ⟨x,hx⟩
  by_cases hh : h ∈ c.H₁ ⊔ c.H₂
  · have hnh : n * h ∉ c.H₁ ⊔ c.H₂ := fun he => hout
      (((c.H₁ ⊔ c.H₂).mul_mem_cancel_right hh).mp he)
    exact (D.mul_mem_cancel_left hnD).mp (outside (n*h) hnh)
  · exact outside h hh

theorem normal_eq_top_of_H_le (N : Subgroup G) [N.Normal] (hHN : c.H ≤ N) : N = ⊤ := by
  let T : Sylow 2 c.H := Classical.choice inferInstance
  obtain ⟨S,hS⟩ := H_sylow_is_ambient c T
  have hSH : (S : Subgroup G) ≤ c.H := hS ▸ map_subtype_le _
  have hnorm : normalizer (S : Set G) ≤ c.H := by
    change normalizer ((S : Subgroup G) : Set G) ≤ c.H
    rw [hS]
    exact H_sylow_normalizer_le c T
  apply top_le_iff.mp
  rw [← S.normalizer_sup_eq_top' (hSH.trans hHN)]
  exact sup_le (hnorm.trans hHN) le_rfl

include c in
/-- A nonidentity ambient normal subgroup cannot have odd order. -/
theorem odd_normal_eq_bot (N : Subgroup G) [N.Normal] (hodd : Odd (Nat.card N)) : N = ⊥ := by
  let D := N.subgroupOf c.H
  let Q := quaternionCore c
  have hDodd : Odd (Nat.card D) := hodd.of_dvd_nat
    (card_dvd_of_injective ((c.H.subtype.comp D.subtype).codRestrict N (fun x => x.property))
      (fun x y hh => Subtype.ext (Subtype.ext (congrArg (fun a : N => (a : G)) hh))))
  have hdis : Q ⊓ D = ⊥ := (disjoint_of_coprime_natCard (by
    rw [quaternionCore_card c]
    exact hDodd.coprime_two_left.pow_left 5)).eq_bot
  have hD : D = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hc : x ∈ centralizer (Q : Set c.H) := by
      rw [mem_centralizer_iff_commutator_eq_one]
      intro q hq
      have hh := commutator_le_inf (H₁ := Q) (H₂ := D) (commutator_mem_commutator hq hx)
      simpa only [hdis,mem_bot] using hh
    exact hdis ▸ (show x ∈ Q ⊓ D from ⟨core_self_centralizing c hc,hx⟩)
  obtain ⟨z,A,hz,hH,_,_,he,hcard,hzA,hf⟩ := exists_fused_four_in_quaternionCore c
  let _ := he
  obtain ⟨t,ht1,htz⟩ := ENat.exists_ne_ne_of_three_le (α := A)
    (by rw [ENat.card_eq_coe_natCard]; exact_mod_cast (by omega : 3 ≤ Nat.card A))
    1 ⟨z,hzA⟩
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hzt : (⟨z,hzA⟩ : A) * t ≠ 1 := by
    intro hh
    apply htz
    apply Subtype.ext
    have heq : (t : c.H) = z⁻¹ := congrArg Subtype.val (eq_inv_of_mul_eq_one_right hh)
    exact heq.trans (inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz2))
  apply normal_eq_bot_of_fused_triple (z : G) (t : c.H) ((orderOf_coe z).trans hz)
    (hf t ht1) (hf ((⟨z,hzA⟩ : A)*t) hzt) N
  intro x hx hxc
  have hxH : x ∈ c.H := hH ▸ hxc
  have hh : (⟨x,hxH⟩ : c.H) ∈ D := hx
  rw [hD,mem_bot] at hh
  exact congrArg Subtype.val hh

include c in
/-- Simplicity follows from the local configuration; it is not an extra hypothesis. -/
theorem ambient_simple : IsSimpleGroup G := by
  obtain ⟨z,hz,_⟩ := exists_involution_centralizer c
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz
  let : Nontrivial G := ⟨⟨z,1,hz1⟩⟩
  refine ⟨fun N hN => ?_⟩
  let := hN
  by_cases hd : 2 ∣ Nat.card N
  · obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := N) 2 hd
    exact Or.inr (normal_eq_top_of_H_le c N
      (H_le_normal_of_involution c N x ((orderOf_coe x).trans hx) x.property))
  · exact Or.inl (odd_normal_eq_bot c N (Nat.odd_iff.mpr (by omega)))

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
