module

public import Theory.SpecificGroups.PSL2.PrimeCardInnerIndex
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.NormalizingInvolutionCard
import Mathlib.Tactic

/-!
# Actual PSL₂ centralizers for the small-prime escape

The literal projective-linear action is an isomorphism onto Aut(PSL₂) over
an odd prime field. Transporting the PGL₂ self-centralizer theorem along it
makes every automorphism four-group self-centralizing. The reflected torus
inside an involution centralizer gives more than eight elements at each of
13, 17, 19, 23. These are the ambient geometric inputs to the escape argument.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript pp.8--9; the torus geometry is Huppert II.8.3--4.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2.SmallPrimeFourGroup

/-- Four-groups in the actual automorphism group of prime-field PSL₂
are self-centralizing. -/
theorem automorphism_four_centralizer (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p) (hF : Nat.card F = p)
    (A : Subgroup (MulAut PSL(2, F))) (hA : IsKleinFour A) :
    centralizer (A : Set (MulAut PSL(2, F))) = A := by
  let hK : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, hp, by omega, by simpa using hF⟩
  have hc : 3 < Nat.card F := by omega
  let e : PGL2 F ≃* MulAut PSL(2, F) := MulEquiv.ofBijective
    (pgl2InnerAutPSL2 F hK hc)
    ⟨pgl2InnerAutPSL2_injective F hK hc, prime_card_pgl_coverage F hF hK hc⟩
  let V := A.map e.symm.toMonoidHom
  have hV : IsKleinFour V := isKleinFour_map_mulEquiv_cross A hA e.symm
  have hVC := pgl2_kleinFour_centralizer_eq_self F hK V hV
  apply le_antisymm
  · intro a ha
    have hcomm : e.symm a ∈ centralizer (V : Set (PGL2 F)) := by
      rw [mem_centralizer_iff]
      rintro x ⟨y, hy, rfl⟩
      change e.symm y * e.symm a = e.symm a * e.symm y
      simpa only [map_mul] using congrArg e.symm ((mem_centralizer_iff.mp ha) y hy)
    rw [hVC] at hcomm
    obtain ⟨a', ha', heq⟩ := hcomm
    have he : a' = a := e.symm.injective heq
    exact he ▸ ha'
  · let : IsKleinFour A := hA
    intro a ha
    rw [mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨x, hx⟩ : A) ⟨a, ha⟩)

/-- At the four source primes every involution centralizer has more than
eight elements. The reflected torus gives the exact twofold count. -/
theorem involution_centralizer_gt_eight (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (hF : Nat.card F = p) (b : PSL(2, F)) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) :
    8 < Nat.card (centralizer ({b} : Set PSL(2, F))) := by
  have ho : Odd p := by rcases hp with rfl | rfl | rfl | rfl <;> decide
  let hK : IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, Fact.out, ho, by omega, by simpa using hF⟩
  obtain ⟨T, s, _, _, hs, hsT, hinv, hC, _, hcard⟩ :=
    psl2_reflected_torus_card hK ⟨hb1, hb2⟩
  have hsN : s ∈ normalizer (T : Set PSL(2, F)) := by
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · rintro x ⟨t, ht, rfl⟩
      change s * t * s⁻¹ ∈ T
      rw [hinv t ht]
      exact T.inv_mem ht
    · rw [card_map_of_injective (MulAut.conj s).injective]
  rw [hC, card_sup_zpowers_of_normalizing_involution T s hs.2 hsT hsN]
  rcases hcard with hcard | hcard <;> rw [hcard, hF]
  all_goals rcases hp with rfl | rfl | rfl | rfl <;> norm_num

end Theory.PSL2.SmallPrimeFourGroup
