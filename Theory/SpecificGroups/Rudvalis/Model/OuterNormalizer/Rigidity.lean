module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level2
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level3
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level4
public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Rigidity.Level5

/-!
# Rigidity of the concrete Rudvalis orbital

Assume the ATLAS-generated subgroup preserves `adj`. Move an arbitrary
relation automorphism's image of zero back to zero by the transitivity
forest, then fix one by the stabilizer forest. Certified color refinements
bound the successive images of two, three and four by the existing word
representatives. Multiplication by their inverses fixes these points in turn.
The last refinement gives distinct colors to all 4060 vertices after five
points have been fixed, so the remaining permutation is the identity.

All finite claims are kernel-checked against the packed relation identified
with `adj` in `Invariance`. The word-subgroup inclusions and fixed-point
facts suffice; no full stabilizer or group-order certificate is used.

Source: the degree-4060 ATLAS model documented in `Model.PermutationData`,
and GLS3 Table 5.3r, printed p.279. This is the conditional relation-rigidity
helper; the unconditional normalizer assembly remains a separate theorem.
-/

namespace Rudvalis.OuterNormalizer
open PrimitiveData OrderCertificate RigidityCertificate

private theorem adjust (hG : modelSubgroup ≤ relationAut)
    (k : Nat) (hk : k < 4060) (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (hf : ∀ x : Fin 4060, x.val < k → p x = x)
    (g : Model) (hg : ∀ x : Fin 4060, x.val < k → g • x = x)
    (hgk : g • (⟨k, hk⟩ : Fin 4060) = p ⟨k, hk⟩)
    (hnext : ∀ q : Equiv.Perm (Fin 4060), q ∈ relationAut →
      (∀ x : Fin 4060, x.val < k + 1 → q x = x) → q ∈ modelSubgroup) :
    p ∈ modelSubgroup := by
  let q : Equiv.Perm (Fin 4060) := g.val⁻¹ * p
  have hq : q ∈ relationAut := relationAut.mul_mem
    (relationAut.inv_mem (hG g.property)) hp
  have hqf (x : Fin 4060) (hx : x.val < k + 1) : q x = x := by
    change g⁻¹ • p x = x
    apply inv_smul_eq_iff.mpr
    by_cases hlt : x.val < k
    · rw [hf x hlt, hg x hlt]
    · have he : x = ⟨k, hk⟩ := Fin.ext (by change x.val = k; omega)
      subst x
      exact hgk.symm
  have hm := modelSubgroup.mul_mem g.property (hnext q hq hqf)
  simpa only [q, mul_inv_cancel_left] using hm

private theorem H2_model : H2 ≤ modelSubgroup := by
  rw [← H0_eq_model]
  exact H2_le.trans H1_le

private theorem H3_model : H3 ≤ modelSubgroup := H3_le.trans H2_model
private theorem H4_model : H4 ≤ modelSubgroup := H4_le.trans H3_model

private theorem fix_four_mem (hG : modelSubgroup ≤ relationAut)
    (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (hf : ∀ x : Fin 4060, x.val < 4 → p x = x) : p ∈ modelSubgroup := by
  obtain ⟨r, hr⟩ := image4_mem_range p hp hf
  let g : Model := ⟨L4Rep r, H4_model (L4Rep_mem r)⟩
  apply adjust hG 4 (by decide) p hp hf g
  · intro x hx
    have h4 := L4Rep_mem r
    have h3 := H4_le h4
    have h2 := H3_le h3
    have h1 := H2_le h2
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
      have : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 := by omega
      simpa only [Fin.ext_iff, show (0 : Fin 4060).val = 0 from rfl,
        show (1 : Fin 4060).val = 1 from rfl,
        show (2 : Fin 4060).val = 2 from rfl,
        show (3 : Fin 4060).val = 3 from rfl] using this
    rcases hx' with rfl | rfl | rfl | rfl
    · exact H1_fix ⟨_, h1⟩
    · exact H2_fix ⟨_, h2⟩
    · exact H3_fix ⟨_, h3⟩
    · exact H4_fix ⟨_, h4⟩
  · exact (L4Rep_point r).trans hr
  · intro q hq hqf
    rw [fix_five_eq_one q hq hqf]
    exact modelSubgroup.one_mem

private theorem fix_three_mem (hG : modelSubgroup ≤ relationAut)
    (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (hf : ∀ x : Fin 4060, x.val < 3 → p x = x) : p ∈ modelSubgroup := by
  obtain ⟨r, hr⟩ := image3_mem_range p hp hf
  let g : Model := ⟨L3Rep r, H3_model (L3Rep_mem r)⟩
  apply adjust hG 3 (by decide) p hp hf g
  · intro x hx
    have h3 := L3Rep_mem r
    have h2 := H3_le h3
    have h1 := H2_le h2
    have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by
      have : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
      simpa only [Fin.ext_iff, show (0 : Fin 4060).val = 0 from rfl,
        show (1 : Fin 4060).val = 1 from rfl,
        show (2 : Fin 4060).val = 2 from rfl,
        show (3 : Fin 4060).val = 3 from rfl] using this
    rcases hx' with rfl | rfl | rfl
    · exact H1_fix ⟨_, h1⟩
    · exact H2_fix ⟨_, h2⟩
    · exact H3_fix ⟨_, h3⟩
  · exact (L3Rep_point r).trans hr
  · exact fix_four_mem hG

private theorem fix_two_mem (hG : modelSubgroup ≤ relationAut)
    (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (hf : ∀ x : Fin 4060, x.val < 2 → p x = x) : p ∈ modelSubgroup := by
  obtain ⟨r, hr⟩ := image2_mem_range p hp hf
  let g : Model := ⟨L2Rep r, H2_model (L2Rep_mem r)⟩
  apply adjust hG 2 (by decide) p hp hf g
  · intro x hx
    have h2 := L2Rep_mem r
    have h1 := H2_le h2
    have hx' : x = 0 ∨ x = 1 := by
      have : x.val = 0 ∨ x.val = 1 := by omega
      simpa only [Fin.ext_iff, show (0 : Fin 4060).val = 0 from rfl,
        show (1 : Fin 4060).val = 1 from rfl,
        show (2 : Fin 4060).val = 2 from rfl,
        show (3 : Fin 4060).val = 3 from rfl] using this
    rcases hx' with rfl | rfl
    · exact H1_fix ⟨_, h1⟩
    · exact H2_fix ⟨_, h2⟩
  · exact (L2Rep_point r).trans hr
  · exact fix_three_mem hG

private theorem fix_one_mem (hG : modelSubgroup ≤ relationAut)
    (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (hf : ∀ x : Fin 4060, x.val < 1 → p x = x) : p ∈ modelSubgroup := by
  have hp0 : p 0 = 0 := hf 0 (by decide)
  have hr : root (p 1) = 1 := by
    have ha : adj 0 1 := by rw [adj_zero]; decide +kernel
    have hb := (hp 0 1).mpr ha
    rw [hp0, adj_zero] at hb
    exact hb
  obtain ⟨g, hg0, hg1⟩ := root_reachable (p 1)
  rw [hr] at hg1
  apply adjust hG 1 (by decide) p hp hf g
  · intro x hx
    have he : x = 0 := Fin.ext (by omega)
    subst x
    exact hg0
  · exact hg1
  · exact fix_two_mem hG

/-- Every automorphism of the concrete orbital lies in the ATLAS-generated
subgroup, provided that subgroup preserves the orbital. -/
public theorem relationAut_le_model (hG : modelSubgroup ≤ relationAut) :
    relationAut ≤ modelSubgroup := by
  intro p hp
  let t := toBase (transDepth (p 0)) (p 0)
  apply adjust hG 0 (by decide) p hp (by intro x hx; omega) t⁻¹
  · intro x hx
    omega
  · exact inv_smul_eq_iff.mpr (toBase_smul (p 0)).symm
  · exact fix_one_mem hG

end Rudvalis.OuterNormalizer
