module
public import Theory.GroupTheory.NormalNonabelianSixteenCenter
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
public import Theory.ElementaryAbelian.Basic

/-!
# Recognition of a non-elementary sixteen with a fixed-point-free automorphism

An automorphism fixes the unique nonidentity element of any characteristic
subgroup of order two. A fixed-point-free automorphism therefore excludes
such subgroups. The elementary order-sixteen center argument then forces
commutativity. The characteristic power kernels and images identify the
non-elementary case with C₄ × C₄.

Source application: Delgado--Goldschmidt--Stellmacher, Groups and Graphs
(1985), proof of (10.9), printed p.163. The argument is intrinsic and does
not require a classification of groups of order sixteen.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.FixedFreeSixteen
variable {H : Type*} [Group H] [Finite H]

private theorem characteristic_card_ne_two (a : MulAut H)
    (hfix : ∀ x : H, a x = x → x = 1)
    (K : Subgroup H) (hK : K.Characteristic) : Nat.card K ≠ 2 := by
  intro hc
  let := hK
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 (by rw [hc])
  have hx1 : (x : H) ≠ 1 := by
    intro he
    have he' : x = 1 := Subtype.ext he
    rw [he',orderOf_one] at hx
    omega
  have haK : a x ∈ K := characteristic_iff_le_comap.mp hK a x.property
  let y : K := ⟨a x,haK⟩
  have hy1 : y ≠ 1 := by
    intro he
    apply hx1
    exact a.injective ((congrArg Subtype.val he).trans a.map_one.symm)
  have he : y = x := by
    obtain ⟨z,hz,hall⟩ := (Nat.card_eq_two_iff' (1 : K)).mp hc
    exact (hall y hy1).trans (hall x (fun he => hx1 (congrArg Subtype.val he))).symm
  exact hx1 (hfix x (congrArg Subtype.val he))

/-- A sixteen admitting a fixed-point-free automorphism is abelian. -/
theorem commutative (hc : Nat.card H = 16) (a : MulAut H)
    (hfix : ∀ x : H, a x = x → x = 1) : IsMulCommutative H := by
  by_contra hn
  obtain ⟨K,hK,hcard,_⟩ := NormalNonabelianSixteen.exists_characteristic_two hc hn
  exact characteristic_card_ne_two a hfix K hK hcard

/-- The non-elementary case is the homocyclic square, with an actual isomorphism. -/
theorem c4_square (hc : Nat.card H = 16) (a : MulAut H)
    (hfix : ∀ x : H, a x = x → x = 1)
    (hne : ¬ IsElementaryAbelian 2 H) :
    Nonempty (H ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let := commutative hc a hfix
  apply NormalSixteenC4Square.recognition_of_no_characteristic_two hc
    (characteristic_card_ne_two a hfix)
  have hn : ∃ x : H, x ^ 2 ≠ 1 := by
    by_contra! hn
    exact hne ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hn⟩
  obtain ⟨x,hx⟩ := hn
  have hd : orderOf x ∣ 2^4 := by simpa [hc] using orderOf_dvd_natCard x
  obtain ⟨n,hn,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · have ho : x = 1 := orderOf_eq_one_iff.mp he
    exact (hx (by rw [ho,one_pow])).elim
  · exact (hx (by simpa only [he,pow_one] using pow_orderOf_eq_one x)).elim
  · exact ⟨x,he⟩
  · exact ⟨x^2,by rw [orderOf_pow,he]; norm_num⟩
  · exact ⟨x^4,by rw [orderOf_pow,he]; norm_num⟩
end Theory.GroupTheory.FixedFreeSixteen
