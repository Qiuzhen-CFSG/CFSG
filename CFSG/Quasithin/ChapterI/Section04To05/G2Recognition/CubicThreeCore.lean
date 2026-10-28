module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.AmbientFusion
public import Theory.GroupAction.KleinFourFactorization.Ambient
public import Theory.GroupTheory.OddInvolutionNormalizer

/-!
# The three-cores of the two cubic centralizers

For the actual common torus, the odd core D of either cubic centralizer
has order 3, 27, or 243 and is the three-core of that centralizer.
Brauer–Wielandt expresses its order as the product of its three torus
centralizer orders. The marked involution fixes the original cubic line;
the common fixed subgroup is trivial because the other involution inverts
that line. An element of the opposite quaternion factor interchanges the
two remaining torus involutions. Thus |D| = 3 |C_D(n)|². Ambient involution
fusion and |C_G(n)| = 576 imply |C_D(n)| divides 9.

The smallest order is equivalent to containment of the literal cubic
normalizer in H. The largest gives 3⁶ dividing |G|. The middle order and
the strongly-three-embedded branch have not been excluded.

This supplies the q=3 odd-core calculation suggested by Fong–Wong,
Nagoya Math. J.36 (1969), §3B and the first paragraph of the proof of §4D,
pp.156, 164–165. It does not assert §4D's dichotomy, which explicitly
excludes q₁=q₂=3. Fong, Nagoya Math. J.39 (1970), §6, p.74, appeals to
Janko for that exceptional case. The complete I.4.5 recognition remains
with `qt-i45-g2-recognition`. `Chapter14CubicThreeCore` applies this family
to the genuine SourceLocalData while retaining both original embeddings.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

theorem cubic_oddCore_odd (x : c.H₁) : Odd (Nat.card (cubicOddCore c x)) := by
  rw [cubicOddCore, card_map_of_injective (cubicCentralizer c x).subtype_injective]
  exact Nat.Coprime.odd_of_left pPrimeCore_coprime_card

include c in
private theorem odd_involution_fixed_card_dvd_nine (D : Subgroup G) (hD : Odd (Nat.card D))
    (u : G) (hu : orderOf u = 2) :
    Nat.card (D ⊓ centralizer ({u} : Set G) : Subgroup G) ∣ 9 := by
  let F := D ⊓ centralizer ({u} : Set G)
  have ho : Odd (Nat.card F) := hD.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F ∣ 64 * 9 := by
    have hh := card_dvd_of_le (show F ≤ centralizer ({u} : Set G) from inf_le_right)
    rwa [involution_centralizer_card c u hu] at hh
  exact (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd

private theorem cubic_oddCore_card_data (x : c.H₁) (hx : orderOf x = 3)
    (z n : c.H) (hz : orderOf z = 2) (hn : orderOf n = 2)
    (hH : c.H = centralizer ({(z:G)} : Set G)) (hzn : z ≠ n)
    (hinv : n*(x:c.H)*n⁻¹ = (x:c.H)⁻¹) :
    Nat.card (cubicOddCore c x) ∣ 3^5 ∧
    Nat.card (cubicOddCore c x) = 3 *
      Nat.card (cubicOddCore c x ⊓ centralizer ({(n:G)} : Set G) : Subgroup G) *
      Nat.card (cubicOddCore c x ⊓ centralizer ({(z:G)*(n:G)} : Set G) : Subgroup G) := by
  let D := cubicOddCore c x
  let C := cubicCentralizer c x
  have hzC : (z:G) ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hH ▸ x.val.property)).symm
  have hnorm : normalizer (C : Set G) ≤ normalizer (D : Set G) :=
    normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)
  have hnN : (n:G) ∈ cubicNormalizer c x := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers ((n:G)*((x:c.H):G)*(n:G)⁻¹) = _
    rw [show (n:G)*((x:c.H):G)*(n:G)⁻¹ = (((x:c.H):G))⁻¹ from congrArg Subtype.val hinv,
      zpowers_inv]
  have hNC : cubicNormalizer c x ≤ normalizer (C : Set G) := by
    have hh := normalizer_le_normalizer_centralizer (zpowers ((x:c.H):G))
    have he : centralizer (zpowers ((x:c.H):G) : Set G) = C := by
      rw [zpowers_eq_closure,centralizer_closure]; rfl
    rwa [he] at hh
  let a : normalizer (D : Set G) := ⟨z,hnorm (C.le_normalizer hzC)⟩
  let b : normalizer (D : Set G) := ⟨n,hnorm (hNC hnN)⟩
  have ha : a^2=1 := Subtype.ext (by
    change (z:G)^2=1
    simpa only [orderOf_coe,hz] using pow_orderOf_eq_one (z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (n:G)^2=1
    simpa only [orderOf_coe,hn] using pow_orderOf_eq_one (n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (hH ▸ n.property)).symm
  have hab2 : orderOf ((z:G)*(n:G))=2 := by
    have hp : ((z:G)*(n:G))^2=1 := by
      have hh := hab.mul_pow 2
      rw [ha,hb,one_mul] at hh
      exact congrArg Subtype.val hh
    have hne : (z:G)*(n:G)≠1 := by
      intro hh
      apply hzn
      apply Subtype.ext
      have hni : (n:G)⁻¹=(n:G) := inv_eq_of_mul_eq_one_left
        (by simpa only [orderOf_coe,hn,pow_two] using pow_orderOf_eq_one (n:G))
      exact (eq_inv_of_mul_eq_one_left hh).trans hni
    exact (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hp) |>.resolve_left
      (fun he => hne (orderOf_eq_one_iff.mp he))
  have hcard := D.card_three_odd_centralizers (cubic_oddCore_odd c x) a b ha hb hab
  have hfix : D ⊓ centralizer ({(a:G)} : Set G) = zpowers ((x:c.H):G) := by
    change D ⊓ centralizer ({(z:G)} : Set G) = _
    rw [←hH]
    exact cubic_oddCore_fixed c x hx
  rw [hfix,Nat.card_zpowers,orderOf_coe,orderOf_coe,hx] at hcard
  have hd : Nat.card D ∣ 3 *
      Nat.card (D ⊓ centralizer ({(b:G)} : Set G) : Subgroup G) *
      Nat.card (D ⊓ centralizer ({((a*b : normalizer (D:Set G)):G)} : Set G) : Subgroup G) := by
    rw [←hcard]
    exact dvd_mul_right _ _
  have hd' : 3 *
      Nat.card (D ⊓ centralizer ({(b:G)} : Set G) : Subgroup G) *
      Nat.card (D ⊓ centralizer ({((a*b : normalizer (D:Set G)):G)} : Set G) : Subgroup G) ∣ 3*9*9 :=
    Nat.mul_dvd_mul (Nat.mul_dvd_mul_left 3
    (odd_involution_fixed_card_dvd_nine c D (cubic_oddCore_odd c x) (n:G)
      ((orderOf_coe n).trans hn)))
    (odd_involution_fixed_card_dvd_nine c D (cubic_oddCore_odd c x) ((z:G)*(n:G)) hab2)
  refine ⟨hd.trans hd',?_⟩
  have hcommon : zpowers ((x:c.H):G) ⊓ centralizer ({(n:G)} : Set G) = ⊥ := by
    apply inf_centralizer_eq_bot_of_odd_inverted _ (by
      rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]; decide)
    intro w hw
    obtain ⟨i,rfl⟩ := mem_zpowers_iff.mp hw
    change (MulAut.conj (n:G)) (((x:c.H):G)^i) = _
    rw [map_zpow]
    change ((n:G)*((x:c.H):G)*(n:G)⁻¹)^i = _
    rw [show (n:G)*((x:c.H):G)*(n:G)⁻¹ = (((x:c.H):G))⁻¹ from congrArg Subtype.val hinv,
      inv_zpow]
  change Nat.card D * Nat.card
    (zpowers ((x:c.H):G) ⊓ centralizer ({(n:G)} : Set G) : Subgroup G)^2 = _ at hcard
  simpa only [hcommon,Subgroup.card_bot,one_pow,mul_one,Subgroup.coe_mul] using hcard

theorem opposite_factor_swaps_torus_involutions (z n : c.H)
    (hline : zpowers z = c.H₁ ⊓ c.H₂) (hn : orderOf n = 2)
    (hout : n ∉ c.H₁ ⊔ c.H₂) :
    ∃ q ∈ c.H₂, q*n*q⁻¹=z*n := by
  let Q := quaternionCore c
  let d := quaternionCoreData c
  have hzI : z ∈ c.H₁.pCoreIn 2 ⊓ c.H₂.pCoreIn 2 :=
    (factor_core_intersection c).symm ▸ (hline ▸ mem_zpowers z)
  let zQ : Q := ⟨z,mem_sup_left hzI.1⟩
  let zz : (d.right ⊓ d.left : Subgroup Q) := ⟨zQ,hzI.2,hzI.1⟩
  let a : MulAut Q := MulAut.conjNormal n
  have ha : a^2=1 := by
    change (MulAut.conjNormal n : MulAut Q)^2=1
    rw [←map_pow,show n^2=1 from hn ▸ pow_orderOf_eq_one n,map_one]
  have ho := outside_bothOuter c n hout
  have hf := (quaternion_outer_involution_factor_data d.right d.left d.right_model
    (by rw [inf_comm]; exact d.intersection_card) a ha ho.right_map ho.right_outer).1 zz
  obtain ⟨q,hq⟩ := (Nat.card_pos_iff.mp (hf.1 ▸ (by decide : 0 < 2))).1
  refine ⟨((q:Q):c.H)⁻¹,c.H₂.inv_mem (c.H₂.pCoreIn_le 2 q.property),?_⟩
  have he := congrArg (fun v : Q => (v:c.H)) hq
  change ((q:Q):c.H)⁻¹ * (n*((q:Q):c.H)*n⁻¹)=z at he
  rw [inv_inv]
  calc
    _ = (((q:Q):c.H)⁻¹ * (n*((q:Q):c.H)*n⁻¹))*n := by group
    _ = z*n := by rw [he]

theorem cubic_oddCore_card_square (x : c.H₁) (hx : orderOf x=3)
    (z n : c.H) (hz : orderOf z=2) (hn : orderOf n=2)
    (hH : c.H = centralizer ({(z:G)} : Set G))
    (hline : zpowers z = c.H₁ ⊓ c.H₂) (hout : n ∉ c.H₁ ⊔ c.H₂)
    (hinv : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹) :
    Nat.card (cubicOddCore c x) = 3 *
      Nat.card (cubicOddCore c x ⊓ centralizer ({(n:G)} : Set G) : Subgroup G)^2 := by
  have hzn : z≠n := by
    intro he
    exact hout (he ▸ mem_sup_left ((hline ▸ mem_zpowers z).1))
  have hp := (cubic_oddCore_card_data c x hx z n hz hn hH hzn hinv).2
  obtain ⟨q,hq,hqn⟩ := opposite_factor_swaps_torus_involutions c z n hline hn hout
  let C := cubicCentralizer c x
  let D := cubicOddCore c x
  have hqC : (q:G) ∈ C := opposite_factor_le_cubic_centralizer c x
    (mem_map_of_mem c.H.subtype hq)
  have hqD : (q:G) ∈ normalizer (D:Set G) :=
    (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C)) (C.le_normalizer hqC)
  have he := D.card_inf_centralizer_conj (q:G) hqD (n:G)
  rw [show (q:G)*(n:G)*(q:G)⁻¹ = (z:G)*(n:G) from congrArg Subtype.val hqn] at he
  change Nat.card D = 3 * Nat.card (D ⊓ centralizer ({(n:G)} : Set G) : Subgroup G) *
    Nat.card (D ⊓ centralizer ({(z:G)*(n:G)} : Set G) : Subgroup G) at hp
  rw [←he,mul_assoc,←pow_two] at hp
  exact hp

theorem cubic_oddCore_orders (x : c.H₁) (hx : orderOf x=3)
    (z n : c.H) (hz : orderOf z=2) (hn : orderOf n=2)
    (hH : c.H = centralizer ({(z:G)} : Set G))
    (hline : zpowers z = c.H₁ ⊓ c.H₂) (hout : n ∉ c.H₁ ⊔ c.H₂)
    (hinv : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹) :
    Nat.card (cubicOddCore c x) = 3 ∨ Nat.card (cubicOddCore c x) = 27 ∨
      Nat.card (cubicOddCore c x) = 243 := by
  have he := cubic_oddCore_card_square c x hx z n hz hn hH hline hout hinv
  have hd := odd_involution_fixed_card_dvd_nine c (cubicOddCore c x)
    (cubic_oddCore_odd c x) (n:G) ((orderOf_coe n).trans hn)
  obtain ⟨i,hi,heq⟩ := (Nat.dvd_prime_pow Nat.prime_three (m := 2)).mp hd
  rw [heq] at he
  interval_cases i <;> norm_num at he <;> simp only [he, true_or, or_true]

private theorem cubic_threeCore_eq_oddCore (x : c.H₁)
    (hp : IsPGroup 3 (cubicOddCore c x)) :
    pCore 3 (cubicCentralizer c x) = pPrimeCore 2 (cubicCentralizer c x) := by
  let C := cubicCentralizer c x
  apply le_antisymm
  · apply le_sSup
    refine ⟨inferInstance,?_⟩
    obtain ⟨i,hi⟩ := (pCore_isPGroup (p := 3) (G := C)).exists_card_eq
    rw [hi]
    exact (by decide : Nat.Coprime 2 3).pow_right _
  · apply le_sSup
    refine ⟨inferInstance,?_⟩
    exact hp.of_equiv ((pPrimeCore 2 C).equivMapOfInjective C.subtype C.subtype_injective).symm

namespace CubicTorus
variable {c} (t : CubicTorus c)
theorem left_oddCore_orders :
    Nat.card (cubicOddCore c t.x) = 3 ∨ Nat.card (cubicOddCore c t.x) = 27 ∨
      Nat.card (cubicOddCore c t.x) = 243 :=
  cubic_oddCore_orders c t.x t.x_order t.z t.n t.z_order t.n_order
    t.centralizer t.central_line t.outside t.invert_left

theorem right_oddCore_orders :
    Nat.card (cubicOddCore (swapFactors c) t.y) = 3 ∨
      Nat.card (cubicOddCore (swapFactors c) t.y) = 27 ∨
      Nat.card (cubicOddCore (swapFactors c) t.y) = 243 :=
  cubic_oddCore_orders (swapFactors c) t.y t.y_order t.z t.n t.z_order t.n_order
    t.centralizer (by change zpowers t.z = c.H₂ ⊓ c.H₁; rw [inf_comm]; exact t.central_line)
    (by change t.n ∉ c.H₂ ⊔ c.H₁; rw [sup_comm]; exact t.outside) t.invert_right

theorem left_oddCore_isThreeGroup : IsPGroup 3 (cubicOddCore c t.x) := by
  apply IsPGroup.of_card_dvd_pow (n := 5)
  rcases t.left_oddCore_orders with h | h | h <;> rw [h] <;> decide

theorem right_oddCore_isThreeGroup : IsPGroup 3 (cubicOddCore (swapFactors c) t.y) := by
  apply IsPGroup.of_card_dvd_pow (n := 5)
  rcases t.right_oddCore_orders with h | h | h <;> rw [h] <;> decide

theorem left_threeCore :
    pCore 3 (cubicCentralizer c t.x) = pPrimeCore 2 (cubicCentralizer c t.x) :=
  cubic_threeCore_eq_oddCore c t.x t.left_oddCore_isThreeGroup

theorem right_threeCore :
    pCore 3 (cubicCentralizer (swapFactors c) t.y) =
      pPrimeCore 2 (cubicCentralizer (swapFactors c) t.y) :=
  cubic_threeCore_eq_oddCore (swapFactors c) t.y t.right_oddCore_isThreeGroup
end CubicTorus

theorem cubic_normalizer_le_H_iff (x : c.H₁) (hx : orderOf x=3) :
    cubicNormalizer c x ≤ c.H ↔ Nat.card (cubicOddCore c x)=3 := by
  have hDC : cubicOddCore c x ≤ cubicCentralizer c x := map_subtype_le _
  have hCN : cubicCentralizer c x ≤ cubicNormalizer c x := by
    change centralizer ({((x:c.H):G)} : Set G) ≤ normalizer (zpowers ((x:c.H):G) : Set G)
    rw [←centralizer_closure,←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hline : Nat.card (zpowers ((x:c.H):G))=3 := by
    rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]
  constructor
  · intro hN
    have he := cubic_oddCore_fixed c x hx
    rw [inf_eq_left.mpr (hDC.trans (hCN.trans hN))] at he
    rw [he,hline]
  · intro hc
    have he : zpowers ((x:c.H):G) = cubicOddCore c x :=
      eq_of_le_of_card_ge (cubic_line_le_oddCore c x hx) (by rw [hc,hline])
    rw [cubic_normalizer_split c x hx,←he]
    exact sup_le (zpowers_le.mpr x.val.property) inf_le_left

theorem cubic_maximal_core_sixth_power_dvd (x : c.H₁) (hx : orderOf x=3)
    (hcard : Nat.card (cubicOddCore c x)=243) : 3^6 ∣ Nat.card G := by
  have hh := card_subgroup_dvd_card (cubicCentralizer c x)
  rw [cubic_centralizer_card c x hx,hcard] at hh
  exact (by decide : 3^6 ∣ 243*24).trans hh

namespace CubicTorus
variable {c} (t : CubicTorus c)
theorem left_three_local_alternative :
    cubicNormalizer c t.x ≤ c.H ∨ Nat.card (cubicOddCore c t.x)=27 ∨ 3^6 ∣ Nat.card G := by
  rcases t.left_oddCore_orders with h | h | h
  · exact Or.inl ((cubic_normalizer_le_H_iff c t.x t.x_order).mpr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (cubic_maximal_core_sixth_power_dvd c t.x t.x_order h))

theorem right_three_local_alternative :
    cubicNormalizer (swapFactors c) t.y ≤ c.H ∨
      Nat.card (cubicOddCore (swapFactors c) t.y)=27 ∨ 3^6 ∣ Nat.card G := by
  rcases t.right_oddCore_orders with h | h | h
  · exact Or.inl ((cubic_normalizer_le_H_iff (swapFactors c) t.y t.y_order).mpr h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (cubic_maximal_core_sixth_power_dvd (swapFactors c) t.y t.y_order h))
end CubicTorus

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
