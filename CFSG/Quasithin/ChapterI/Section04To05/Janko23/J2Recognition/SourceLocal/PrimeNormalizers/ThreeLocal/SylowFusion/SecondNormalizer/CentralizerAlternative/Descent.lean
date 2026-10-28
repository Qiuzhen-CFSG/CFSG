module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.Basic
public import Theory.GroupTheory.OddCentralInvolutionLifting

/-!
# Full involution geometry in the cubic quotient

Odd central kernels give unique square-one lifts. Consequently the full
centralizer of an involution is the inverse image of its quotient
centralizer, and fusion of all involutions descends. A centralizer of
order twelve and exponent dividing six descends to a Klein four-group.

The application uses the literal projection C_G(⟨y⟩) → C_G(⟨y⟩)/⟨y⟩.
This verifies the input to the order-four Brauer–Suzuki–Wall branch,
conditional on the actual local geometry, rather than applying recognition
to a calculation for just one involution.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262;
*Finite Group Theory*, second edition, Exercise 16.6, pp.266–267.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

private theorem centralizer_comap_of_odd_central_kernel
    {A B : Type*} [Group A] [Group B] (q : A →* B)
    (hodd : Odd (Nat.card q.ker)) (hc : q.ker ≤ center A)
    {t : A} (ht : t ^ 2 = 1) :
    (centralizer ({q t} : Set B)).comap q = centralizer ({t} : Set A) := by
  ext a
  simp only [mem_comap, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have he : a * t * a⁻¹ = t := by
      apply OddCentralLifting.involution_lift_unique q hodd hc
      · change (MulAut.conj a t) ^ 2 = 1
        rw [← map_pow, ht, map_one]
      · exact ht
      · rw [map_mul, map_mul, map_inv, h, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h
    simpa only [map_mul] using congrArg q h

private theorem card_map_mul_kernel {A B : Type*} [Group A] [Group B]
    (q : A →* B) (U : Subgroup A) (hker : q.ker ≤ U) :
    Nat.card (U.map q) * Nat.card q.ker = Nat.card U := by
  have h := (q.ker.subgroupOf U).index_mul_card
  change q.ker.relIndex U * Nat.card (q.ker.subgroupOf U) = Nat.card U at h
  rw [relIndex_ker, Nat.card_congr (subgroupOfEquivOfLe hker).toEquiv] at h
  exact h

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The complete order-four involution-centralizer input on the literal quotient.
Every quotient involution is covered by the fusion conclusion. -/
theorem quotient_dihedral_geometry
    {S : InvolutionGeometry.SelectedGeometry D} {y : G} (hyo : orderOf y = 3)
    (L : CubicLocalGeometry S y) :
    Nonempty (DihedralInvolutionCentralizerHypotheses (CubicQuotient y) 2) := by
  let q := cubicQuotientMap y
  have hq : Function.Surjective q := cubicQuotientMap_surjective y
  have hk : Nat.card q.ker = 3 := by rw [cubicQuotientMap_ker, cubicKernel_card hyo]
  have hodd : Odd (Nat.card q.ker) := by rw [hk]; decide
  have hc : q.ker ≤ center (cubicCentralizer y) := by
    rw [cubicQuotientMap_ker]
    exact cubicKernel_le_center y
  have hu2 : L.u ^ 2 = 1 := L.u_order ▸ pow_orderOf_eq_one L.u
  have huq : GorensteinWalter.IsInvolution (q L.u) := by
    refine ⟨?_, by rw [← map_pow, hu2, map_one]⟩
    intro he
    have hu1 := OddCentralLifting.kernel_involution_eq_one q hodd he hu2
    have hh := L.u_order
    rw [hu1, orderOf_one] at hh
    omega
  let U := centralizer ({L.u} : Set (cubicCentralizer y))
  let V := centralizer ({q L.u} : Set (CubicQuotient y))
  have hcomap : V.comap q = U := centralizer_comap_of_odd_central_kernel q hodd hc hu2
  have hmap : U.map q = V := by
    rw [← hcomap, map_comap_eq_self_of_surjective hq]
  have hker : q.ker ≤ U := hc.trans (center_le_centralizer _)
  have hvcard : Nat.card V = 4 := by
    have hh := card_map_mul_kernel q U hker
    rw [hmap, hk, L.centralizer_card] at hh
    omega
  have hvpow (x : V) : x ^ 2 = 1 := by
    obtain ⟨a, ha, hax⟩ := (show (x : CubicQuotient y) ∈ U.map q by
      rw [hmap]
      exact x.property)
    have hx6 : x ^ 6 = 1 := by
      apply Subtype.ext
      change (x : CubicQuotient y) ^ 6 = 1
      rw [← hax, ← map_pow]
      have hh : a ^ 6 = 1 := congrArg Subtype.val (L.centralizer_pow ⟨a, ha⟩)
      rw [hh, map_one]
    have hd4 : orderOf x ∣ 4 := by simpa only [hvcard] using orderOf_dvd_natCard x
    exact orderOf_dvd_iff_pow_eq_one.mp
      (show orderOf x ∣ 2 from Nat.dvd_gcd hd4 (orderOf_dvd_of_pow_eq_one hx6))
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hvcard]; decide)
  let : IsKleinFour V := ⟨hvcard, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr
    (fun x hx => orderOf_eq_prime (hvpow x) hx)⟩
  refine ⟨{
    two_le := le_rfl
    z := q L.u
    involution := huq
    involutions_conjugate := ?_
    centralizer_equiv := by
      change Nonempty (V ≃* DihedralGroup 2)
      exact IsKleinFour.nonempty_mulEquiv
  }⟩
  intro b hb
  obtain ⟨a, hab, ha2⟩ := OddCentralLifting.exists_involution_lift q hodd hq b hb.2
  have hao : orderOf a = 2 := orderOf_eq_prime ha2 (fun he => hb.1 (by
    rw [← hab, he, map_one]))
  obtain ⟨g, hg⟩ := isConj_iff.mp (L.involutions_conjugate a hao)
  refine ⟨q g, ?_⟩
  rw [← hab]
  simpa only [map_mul, map_inv] using congrArg q hg

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
