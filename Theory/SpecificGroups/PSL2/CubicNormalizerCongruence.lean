module

public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import GorensteinWalter.CardSupOfDisjointNormalizer
public import GorensteinWalter.PGL2KleinFourSelfCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
/-!
# Cubic normalizers in prime PSL₂

A four-group normalizing a cubic subgroup has an involution in the kernel
of its action. The involution centralizer contains both subgroups, so its
order is divisible by twelve. The actual reflected-torus calculation gives
centralizer order p−1 or p+1. For p congruent to 3 or 5 modulo eight this
forces p congruent to 11 or 13 modulo twenty-four.

This is the common numerical step in Aschbacher--Smith F.6.17 and the
prime PSL₂ rows of F.6.18, printed pp.309–310. The normalizing four-group
and cubic are the supplied subgroups, not assumed local model outputs.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups

namespace Theory.PSL2
variable {F : Type*} [Field F] [Finite F]
theorem involution_centralizer_card_cases (hF : IsOddPrimePower (Nat.card F)) (t : PSL(2,F)) (ht : IsInvolution t) :
    Nat.card (centralizer ({t} : Set PSL(2,F))) = Nat.card F - 1 ∨
    Nat.card (centralizer ({t} : Set PSL(2,F))) = Nat.card F + 1 := by
  obtain ⟨T,s,_,_,hs,hsT,hinv,hC,_,hcard⟩ := psl2_reflected_torus_card hF ht
  have hn : zpowers s ≤ normalizer (T : Set PSL(2,F)) := by
    apply zpowers_le.mpr
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact T.inv_mem hx
    · intro hx
      have hh := T.inv_mem hx
      have he : s * (s * x * s⁻¹) * s⁻¹ = x := by
        calc
          _ = (s*s) * x * (s*s)⁻¹ := by group
          _ = x := by rw [← pow_two,hs.2]; simp
      rwa [← hinv _ hx,he] at hh
  have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  have hds : Disjoint T (zpowers s) := by
    apply disjoint_def.mpr
    intro x hx hxS
    have hcases : x = 1 ∨ x = s := by
      have hcard : Nat.card (zpowers s) = 2 := by rw [Nat.card_zpowers,hsord]
      have hh := (Nat.card_eq_two_iff' (1 : zpowers s)).mp hcard
      obtain ⟨a,ha,hrest⟩ := hh
      by_cases hx1 : x=1
      · exact Or.inl hx1
      · right
        have haS := hrest ⟨s,mem_zpowers s⟩ (by intro he; exact hs.1 (congrArg Subtype.val he))
        have haX := hrest ⟨x,hxS⟩ (by intro he; exact hx1 (congrArg Subtype.val he))
        exact congrArg Subtype.val (haX.trans haS.symm)
    rcases hcases with h | rfl
    · exact h
    · exact (hsT hx).elim
  have hc : Nat.card (centralizer ({t} : Set PSL(2,F))) = Nat.card T * 2 := by
    rw [hC,card_sup_eq_mul_of_disjoint_of_le_normalizer T (zpowers s) hn hds,
      Nat.card_zpowers,hsord]
  have ho : Odd (Nat.card F) := by
    obtain ⟨p,f,_,ho,_,he⟩ := hF
    rw [he]
    exact ho.pow
  obtain ⟨k,hk⟩ := ho
  rcases hcard with hcT|hcT
  · left
    omega
  · right
    omega


private theorem four_normalizing_cubic_has_fixed_involution
    {G : Type*} [Group G] [Finite G] (V A : Subgroup G) [IsKleinFour V]
    (hA : Nat.card A = 3) (hn : V ≤ normalizer (A : Set G)) :
    ∃ t : G, t ∈ V ∧ IsInvolution t ∧ t ∈ centralizer (A : Set G) := by
  let : IsCyclic A := isCyclic_of_prime_card hA
  let f : V →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  have hAut : Nat.card (MulAut A) = 2 := by rw [IsCyclic.card_mulAut,hA]; decide
  have hker : f.ker ≠ ⊥ := by
    intro he
    have hh := Nat.card_le_card_of_injective f (f.ker_eq_bot_iff.mp he)
    rw [IsKleinFour.card_four,hAut] at hh
    omega
  let : Nontrivial f.ker := (Subgroup.nontrivial_iff_ne_bot f.ker).mpr hker
  obtain ⟨x,hx⟩ := exists_ne (1 : f.ker)
  let t : G := x.val.val
  have ht1 : t ≠ 1 := by
    intro hh
    apply hx
    apply Subtype.ext
    exact Subtype.ext hh
  have ht2 : t ^ 2 = 1 := by
    have hh := Monoid.pow_exponent_eq_one x.val
    rw [IsKleinFour.exponent_two] at hh
    exact congrArg (fun v : V => (v : G)) hh
  refine ⟨t,x.val.property,⟨ht1,ht2⟩,?_⟩
  intro a ha
  have hh := congrArg (fun b : MulAut A => b ⟨a,ha⟩) (MonoidHom.mem_ker.mp x.property)
  have hg : t * a * t⁻¹ = a := congrArg Subtype.val hh
  exact (mul_inv_eq_iff_eq_mul.mp hg).symm

theorem prime_mod24_of_four_normalizes_cubic {p : ℕ} [Fact p.Prime] (hp : Odd p) (h8 : p % 8 = 3 ∨ p % 8 = 5)
    (V A : Subgroup PSL(2,ZMod p)) [IsKleinFour V]
    (hA : Nat.card A = 3) (hn : V ≤ normalizer (A : Set PSL(2,ZMod p))) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  obtain ⟨t,htV,ht,htA⟩ := four_normalizing_cubic_has_fixed_involution V A hA hn
  let C := centralizer ({t} : Set PSL(2,ZMod p))
  have hAC : A ≤ C := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (htA a ha)
  have hVC : V ≤ C := by
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((IsKleinFour.isMulCommutative (G := V)).is_comm.comm
      (⟨v,hv⟩ : V) ⟨t,htV⟩)
  have hthree : 3 ∣ Nat.card C := hA ▸ card_dvd_of_le hAC
  have hfour : 4 ∣ Nat.card C := IsKleinFour.card_four (G := V) ▸ card_dvd_of_le hVC
  have htwelve : 12 ∣ Nat.card C :=
    (show Nat.Coprime 3 4 by decide).mul_dvd_of_dvd_of_dvd hthree hfour
  have hF : IsOddPrimePower (Nat.card (ZMod p)) := ⟨p,1,Fact.out,hp,by omega,by simp⟩
  have hc := involution_centralizer_card_cases hF t ht
  simp only [Nat.card_zmod] at hc
  have hp2 := (Fact.out : p.Prime).two_le
  rcases hc with hc|hc <;> change Nat.card C = _ at hc
  all_goals rw [hc] at htwelve
  all_goals omega
end Theory.PSL2
