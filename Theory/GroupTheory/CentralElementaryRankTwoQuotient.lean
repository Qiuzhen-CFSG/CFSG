module

public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.ElementaryAbelian.Quotient
public import Theory.Quasithin.Rank

/-!
# Three-rank in small quotients by an elementary central subgroup

Let Z be central elementary abelian of order dividing nine, with index at most
nine. If the three-rank of P is at most two, quotienting by any subgroup of Z
preserves that bound. No prime-group assumption on P is required.

A larger elementary quotient would force |P|=81, |Z|=9 and a cubic kernel.
Commutators then are central of exponent three, so cubing is a homomorphism
into that kernel. Rank at most two makes every cubic element lie in Z:
an element outside Z would generate an elementary group of order27 with Z.
The cube map would consequently have kernel of order at most nine and image
of order at most three, contradicting |P|=81.

The surjective-map theorem retains actual maps; the quotient applications use
the literal quotient projections. The normal instances for central subgroups
are routine and introduce no additional group-theoretic hypothesis.

Source application: the PSU₄(3) partial-central-quotient step in
Aschbacher–Smith A.2.17, retaining the ordinary-rank assertion of I.2.1.
The cubic collection identity is the class-two calculation also used in
`PGroup.OrderTwentySeven.cube_mul`.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CentralExtension

private theorem cube_mul_of_central_cubic_commutator {P : Type*} [Group P]
    (x y : P) (hc : ⁅y,x⁆ ∈ center P) (hc3 : ⁅y,x⁆^3=1) :
    (x*y)^3=x^3*y^3 := by
  let c := ⁅y,x⁆
  have hswap : y*x=c*x*y := by simp [c,commutatorElement_def,mul_assoc]
  have hxc : x*c=c*x := mem_center_iff.mp hc x
  have hyc : y*c=c*y := mem_center_iff.mp hc y
  have hxca (z : P) : x*(c*z)=c*(x*z) := by rw [← mul_assoc,hxc,mul_assoc]
  have hyca (z : P) : y*(c*z)=c*(y*z) := by rw [← mul_assoc,hyc,mul_assoc]
  have hs (z : P) : y*(x*z)=c*(x*(y*z)) := by
    rw [← mul_assoc,hswap]; simp only [mul_assoc]
  calc
    (x*y)^3 = c^3*(x^3*y^3) := by
      simp only [pow_succ,pow_zero,one_mul,mul_assoc,hs,hxca,hyca]
    _ = x^3*y^3 := by rw [hc3,one_mul]

public theorem threeRank_le_two_of_surjective
    {P Q : Type*} [Group P] [Finite P] [Group Q]
    (Z : Subgroup P) [IsElementaryAbelian 3 Z]
    (hZc : Z ≤ center P) (hZcard : Nat.card Z ∣ 9) (hZi : Z.index ≤ 9)
    (f : P →* Q) (hf : Function.Surjective f) (hker : f.ker ≤ Z)
    (hrank : primeRank 3 P ≤ 2) : primeRank 3 Q ≤ 2 := by
  let : Finite Q := Finite.of_surjective f hf
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZle : Nat.card Z ≤ 9 := Nat.le_of_dvd (by decide) hZcard
  have hP : Nat.card P ≤ 81 := by
    have he := Z.card_mul_index
    nlinarith
  have hPcard : Nat.card P=Nat.card Q * Nat.card f.ker := by
    rw [← f.ker.index_mul_card,index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
  have hkd : Nat.card f.ker ∣ 9 := (Subgroup.card_dvd_of_le hker).trans hZcard
  have hkcases : Nat.card f.ker=1 ∨ Nat.card f.ker=3 ∨ Nat.card f.ker=9 := by
    have hh := Nat.mem_divisors.mpr ⟨hkd,(by decide : 9 ≠ 0)⟩
    have he : Nat.divisors 9={1,3,9} := by decide
    simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hh
  rcases hkcases with hk1 | hk3 | hk9
  · have hi : Function.Injective f := f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq hk1)
    rwa [← primeRank_congr 3 (MulEquiv.ofBijective f ⟨hi,hf⟩)]
  all_goals
    by_contra hbad
    obtain ⟨A,hA,hAc⟩ := exists_elementaryAbelian_card_primeRank (G:=Q) (p:=3)
    have hA27 : 27 ≤ Nat.card A := by
      rw [hAc]
      exact Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ primeRank 3 Q)
    have hQ27 : 27 ≤ Nat.card Q := hA27.trans A.card_le_card_group
  case inr.inr => nlinarith [hPcard]
  have hQ : Nat.card Q=27 := by nlinarith [hPcard]
  have hP81 : Nat.card P=81 := by rw [hPcard,hQ,hk3]
  have hZ9 : Nat.card Z=9 := by
    have he := Z.card_mul_index
    nlinarith
  have hAtop : A=⊤ := (Subgroup.card_eq_iff_eq_top A).mp (by
    have hAle := A.card_le_card_group
    omega)
  let : IsElementaryAbelian 3 A := hA
  let : IsElementaryAbelian 3 Q := IsElementaryAbelian.of_surjective A.subtype (by
    apply MonoidHom.range_eq_top.mp
    rw [Subgroup.range_subtype,hAtop])
  have hc (x y : P) : ⁅x,y⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  have hcube (x : P) : x^3 ∈ f.ker := by
    rw [MonoidHom.mem_ker,map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 Q) _
  let cube : P →* f.ker := {
    toFun := fun x => ⟨x^3,hcube x⟩
    map_one' := Subtype.ext (one_pow 3)
    map_mul' := fun x y => Subtype.ext (cube_mul_of_central_cubic_commutator x y
      (hZc (hker (hc y x))) (elemPow_eq_one_of_isElementaryAbelian _ (hker (hc y x)))) }
  have hKle : cube.ker ≤ Z := by
    intro x hx
    by_contra hxZ
    have hx3 : x^3=1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hx1 : x ≠ 1 := fun he => hxZ (he ▸ Z.one_mem)
    have hfix : Z ≤ centralizer ({x} : Set P) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp (hZc hz) x).symm)
    have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join Z x
      (orderOf_eq_prime hx3 hx1) hxZ hfix (show Nat.card Z=3^2 from hZ9)
    omega
  have hK9 : Nat.card cube.ker ≤ 9 := (Subgroup.card_le_of_le hKle).trans_eq hZ9
  have hR3 : Nat.card cube.range ≤ 3 := cube.range.card_le_card_group.trans_eq hk3
  have he := cube.ker.card_mul_index
  rw [Subgroup.index_ker] at he
  nlinarith

/-- Literal central quotient application, with the index hypothesis on Z. -/
public theorem threeRank_quotient_le_two_of_index
    {P : Type*} [Group P] [Finite P]
    (Z B : Subgroup P) [B.Normal] [IsElementaryAbelian 3 Z]
    (hZc : Z ≤ center P) (hZcard : Nat.card Z ∣ 9) (hZi : Z.index ≤ 9)
    (hBZ : B ≤ Z) (hrank : primeRank 3 P ≤ 2) : primeRank 3 (P ⧸ B) ≤ 2 := by
  exact threeRank_le_two_of_surjective Z hZc hZcard hZi
    (QuotientGroup.mk' B) (QuotientGroup.mk'_surjective B)
    (by simpa only [QuotientGroup.ker_mk'] using hBZ) hrank

/-- The source formulation using the size of the quotient by the elementary center. -/
public theorem threeRank_quotient_le_two
    {P : Type*} [Group P] [Finite P]
    (Z B : Subgroup P) [Z.Normal] [B.Normal] [IsElementaryAbelian 3 Z]
    (hZc : Z ≤ center P) (hZcard : Nat.card Z ≤ 9) (hQcard : Nat.card (P ⧸ Z) ≤ 9)
    (hBZ : B ≤ Z) (hrank : primeRank 3 P ≤ 2) : primeRank 3 (P ⧸ B) ≤ 2 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 Z).exists_card_eq
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 3)).mp (by
    simpa only [← hn] using hZcard)
  exact threeRank_quotient_le_two_of_index Z B hZc (by
    rw [hn]
    exact pow_dvd_pow 3 hn2) (by rwa [index_eq_card]) hBZ hrank

end CentralExtension
