module

public import Stellmacher.SectionOne.ExceptionalOddComplement

/-!
# The elementary structure of the order-nine odd core

An elementary subgroup of order four acts faithfully by conjugation on
the order-nine odd core under the Section One hypotheses. A cyclic nine
has only six automorphisms, so this action rules out cyclicity. The odd
core is consequently elementary abelian of order nine.

The elementary four need not be Sylow. This supplies the representation
input for Stellmacher (9.1)(8), printed p.47, PDF page 37 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionOne

universe u

public theorem nineCore_elementary_of_elementary_four
    {K V : Type u} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (h : Hypotheses K V) (hoddcard : Nat.card (oddCore K) = 9)
    (X : Subgroup K) (hX : IsElementaryAbelian 2 X) (hXcard : Nat.card X = 4) :
    IsElementaryAbelian 3 (oddCore K) := by
  let W := oddCore K
  let _ : W.Normal := pPrimeCore_normal
  have hWp : IsPGroup 3 W := IsPGroup.of_card (p := 3) (n := 2) hoddcard
  have hcent : X ⊓ Subgroup.centralizer (W : Set K) = ⊥ :=
    RankOneThreeGroupAssembly.sylow_inf_centralizer_oddCore_eq_bot h X hX hWp
  let conjugation : X →* MulAut W := MulAut.conjNormal.comp X.subtype
  have hinj : Function.Injective conjugation := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subtype.ext
    apply hcent.le
    refine ⟨x.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro w hw
    have heq := congrArg (fun automorphism : MulAut W => (automorphism ⟨w, hw⟩ : K))
      (MonoidHom.mem_ker.mp hx)
    change (x : K) * w * (x : K)⁻¹ = w at heq
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  have hnotcyclic : ¬ IsCyclic W := by
    intro hcyclic
    let _ : IsCyclic W := hcyclic
    have hAut : Nat.card (MulAut W) = 6 := by
      rw [IsCyclic.card_mulAut, hoddcard]
      decide
    have hbad := Subgroup.card_dvd_of_injective conjugation hinj
    rw [hXcard, hAut] at hbad
    norm_num at hbad
  have hWcomm : IsMulCommutative W :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hoddcard
  have hWexp : Monoid.exponent W = 3 :=
    (not_isCyclic_iff_exponent_eq_prime Nat.prime_three hoddcard).mp hnotcyclic
  exact { toIsMulCommutative := hWcomm, exponent_dvd_p := by rw [hWexp] }

end Stellmacher.SectionOne
