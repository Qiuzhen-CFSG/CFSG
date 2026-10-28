module
public import Theory.GroupTheory.PResidual.ThreeFree
public import Theory.PPrimeCore

/-!
# Prime-to-three cores in two-reduced {2,3} quotients

A surjection to a {2,3}-group with trivial two-core kills the source's
prime-to-three core: its normal image is a three-free {2,3}-group, hence
a two-group. This gives the literal quotient factorization used in
Aschbacher–Smith 14.5.11(2), pp.1015–1016, refs/quasithin.pdf.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- The source prime-to-three core lies in the actual quotient kernel. -/
theorem pPrimeCore_three_le_kernel_of_twoThree
    (f : G →* H) (hf : Function.Surjective f)
    (hH : IsPiGroup twoThreePrimes H) (hcore : pCore 2 H = ⊥) :
    pPrimeCore 3 G ≤ f.ker := by
  let N := (pPrimeCore 3 G).map f
  have hn : N.Normal := Normal.map inferInstance f hf
  have h23 : IsPiGroup twoThreePrimes N := hH.of_injective N.subtype N.subtype_injective
  have h3 : ¬ 3 ∣ Nat.card N := Nat.prime_three.coprime_iff_not_dvd.mp
    (pPrimeCore_coprime_card.of_dvd_right (card_map_dvd (pPrimeCore 3 G) f))
  have hN : IsPGroup 2 N := isPGroup_two_of_isPiGroup_twoThree h23 h3
  have hz : N = ⊥ := bot_unique ((le_sSup ⟨hn,hN⟩ : N ≤ pCore 2 H).trans_eq hcore)
  exact (Subgroup.map_eq_bot_iff _).mp hz
end Theory.GroupTheory
