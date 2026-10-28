module
public import CFSG.Quasithin.FermatMersenne
public import Theory.SpecificGroups.PSL2.FourNormalizer

/-!
# Four-normalizers for the surviving prime-linear source family

The exact 2.5.2(4) predicate says that p>7 is a Fermat or Mersenne prime.
One of p-1,p+1 is therefore a power of two at least sixteen, so the intrinsic
PSL₂ four-normalizer theorem applies. Transport retains the original F≤K
and its actual subgroup inside K.

This supplies C_K(F)=F and the intrinsic N_K(F)≃S₄ clause of
Aschbacher–Smith 2.5.8(5), printed pp.556–557. The ambient automorphism
containment remains with the full small-model assembly.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection

private theorem source_prime_adjacent_eight {p : ℕ}
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p) :
    8 ∣ p - 1 ∨ 8 ∣ p + 1 := by
  rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
  · have ha2 : 2 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    have he : 3 ≤ 2 ^ a := by
      have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) ha2
      norm_num at this
      omega
    left
    rw [show p - 1 = 2 ^ (2 ^ a) by omega]
    exact pow_dvd_pow 2 he
  · have ha3 : 3 ≤ a := by
      by_contra! h
      interval_cases a <;> norm_num at ha <;> omega
    right
    rw [ha]
    exact pow_dvd_pow 2 ha3

/-- The complete intrinsic normalizer calculation for the source's prime parameter. -/
theorem linear_prime_four_normalizer (p : ℕ) [Fact p.Prime]
    (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (F : Subgroup PSL(2,ZMod p)) [IsKleinFour F] :
    Nonempty (normalizer (F : Set PSL(2,ZMod p)) ≃* Equiv.Perm (Fin 4)) :=
  Theory.PSL2.FourNormalizer.prime_four_normalizer p (hp.1.odd_of_ne_two (by omega))
    (source_prime_adjacent_eight hp hbig) F

/-- Both intrinsic 2.5.8(5) conclusions on the original prime-linear component. -/
theorem linear_prime_four_structure {G : Type*} [Group G]
    (K F : Subgroup G) (hFK : F ≤ K) [IsKleinFour F]
    (p : ℕ) [Fact p.Prime] (hp : IsFermatOrMersennePrime p) (hbig : 7 < p)
    (e : K ≃* PSL(2,ZMod p)) :
    centralizer (F.subgroupOf K : Set K) = F.subgroupOf K ∧
      Nonempty (normalizer (F.subgroupOf K : Set K) ≃* Equiv.Perm (Fin 4)) := by
  let U := F.subgroupOf K
  let A := U.map e.toMonoidHom
  let eF := (e.subgroupMap U).symm.trans (subgroupOfEquivOfLe hFK)
  let : IsKleinFour A :=
    { card_four := (Nat.card_congr eF.toEquiv).trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).trans IsKleinFour.exponent_two }
  have hodd : Odd p := hp.1.odd_of_ne_two (by omega)
  have hc := Theory.PSL2.FourNormalizer.four_centralizer
    (K := ZMod p) ⟨p,1,Fact.out,hodd,by decide,by simp⟩ A
  let : IsMulCommutative F := IsKleinFour.isMulCommutative
  constructor
  · apply le_antisymm _ U.le_centralizer
    intro x hx
    have he : e x ∈ centralizer (A : Set PSL(2,ZMod p)) :=
      map_centralizer_le_centralizer_image (U : Set K) e.toMonoidHom ⟨x,hx,rfl⟩
    rw [hc] at he
    simpa only [e.symm_apply_apply] using (mem_map_equiv (f := e)).mp he
  · obtain ⟨h⟩ := linear_prime_four_normalizer p hp hbig A
    exact ⟨((e.subgroupMap (normalizer (U : Set K))).trans
      (MulEquiv.subgroupCongr (map_equiv_normalizer_eq U e))).trans h⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
