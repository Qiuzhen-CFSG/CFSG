module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupAction.SubgroupConjugation

/-!
# Normality from a trivial quotient action

Let L be normal in G and N characteristic in L. If N ≤ R and R acts
trivially on L/N, then L normalizes R. Apply the quotient identity to l⁻¹:
the difference l r l⁻¹ r⁻¹ belongs to N, hence l r l⁻¹ belongs to R.
All normality assertions retain their actual ambient group.

Source application: Aschbacher–Smith, proof of Proposition 1.3.8,
combined manuscript of 1 March 2004, printed p.513, with N = O₂(L).
-/

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A trivial action on L/N gives L-invariance of R when N is contained in R. -/
public theorem le_normalizer_of_trivial_normalQuotientAction
    (L R : Subgroup G) [L.Normal] (N : Subgroup L) [N.Characteristic]
    (hNR : N.map L.subtype ≤ R)
    (hfix : ∀ r ∈ R, normalQuotientAction L N r = 1) :
    L ≤ normalizer (R : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl r hr
  let a : L := ⟨l, hl⟩
  have he := congrArg (fun f : MulAut (L ⧸ N) => f (QuotientGroup.mk' N a⁻¹))
    (hfix r hr)
  rw [normalQuotientAction_apply_mk] at he
  have hm : (a⁻¹)⁻¹ * MulAut.conjNormal r a⁻¹ ∈ N := QuotientGroup.eq.mp he.symm
  have hn := hNR (mem_map.mpr ⟨_, hm, rfl⟩)
  have hmR := R.mul_mem hn hr
  have hc : ((MulAut.conjNormal r a⁻¹ : L) : G) = r * l⁻¹ * r⁻¹ := rfl
  simp only [inv_inv] at hmR
  change (l * ((MulAut.conjNormal r a⁻¹ : L) : G)) * r ∈ R at hmR
  rw [hc] at hmR
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hmR
end Subgroup
