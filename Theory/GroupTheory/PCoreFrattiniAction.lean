module

public import Theory.PGroupCore
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# The exact action kernel on a self-centralizing core's Frattini quotient

For a finite group with self-centralizing p-core, where p is prime, the
canonical conjugation action on that core modulo its Frattini subgroup has
kernel exactly the p-core. Thus the ambient quotient by the p-core acts
faithfully on this literal elementary abelian quotient. Solvability and
any bound on the quotient dimension are unnecessary.

The kernel of conjugation on the core is a p-group by self-centralization.
Burnside's Frattini automorphism kernel is also a p-group; its preimage is
therefore a normal p-group and lies in the ambient p-core. Conversely,
inner conjugation by core elements is trivial on the abelian Frattini
quotient. Both directions concern the same canonical composition of
`MulAut.conjNormal` and `Subgroup.quotientAut`.

This standard Burnside--Frattini argument is the reusable kernel step of
`CharacteristicTwoFrattiniEightBound` and supports the full involution
centralizer quotient in the large terminal recognition branch.
-/

namespace Subgroup
open scoped IsMulCommutative

public theorem pCore_frattini_action_kernel
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact (Nat.Prime p)]
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G) :
    ((quotientAut (frattini (pCore p G))).comp
      (MulAut.conjNormal : G →* MulAut (pCore p G))).ker = pCore p G := by
  let Q := pCore p G
  have hQ : IsPGroup p Q := pCore_isPGroup
  let _ : Fact (IsPGroup p Q) := ⟨hQ⟩
  let V := Q ⧸ frattini Q
  let _ : IsElementaryAbelian p V := isElementaryAbelian_quotient_frattini (p := p)
  let conjugation : G →* MulAut Q := MulAut.conjNormal
  let action : G →* MulAut V := (quotientAut (frattini Q)).comp conjugation
  have hconjker : conjugation.ker ≤ Q := by
    intro g hg
    apply hcentral
    rw [mem_centralizer_iff]
    intro q hq
    have hfix := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G))
      (MonoidHom.mem_ker.mp hg)
    change g * q * g⁻¹ = q at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hkernel : IsPGroup p action.ker :=
    (isPGroup_quotientAut_frattini_kernel hQ).comap_of_ker_isPGroup
      conjugation (hQ.to_le hconjker)
  apply le_antisymm (show action.ker ≤ pCore p G from le_sSup ⟨inferInstance, hkernel⟩)
  intro g hg
  rw [MonoidHom.mem_ker]
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (frattini Q) v
  change quotientAut (frattini Q) (conjugation g)
    (QuotientGroup.mk' (frattini Q) q) = QuotientGroup.mk' (frattini Q) q
  rw [quotientAut_apply_mk]
  change QuotientGroup.mk' (frattini Q)
    ((⟨g, hg⟩ : Q) * q * (⟨g, hg⟩ : Q)⁻¹) = QuotientGroup.mk' (frattini Q) q
  rw [map_mul, map_mul, map_inv,
    mul_comm (QuotientGroup.mk' (frattini Q) (⟨g, hg⟩ : Q))
      (QuotientGroup.mk' (frattini Q) q), mul_inv_cancel_right]

end Subgroup
