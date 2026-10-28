module
public import Stellmacher.SectionThree.LemmaThreeThree
public import Stellmacher.TwoResidualIdentification

/-!
# Odd prime-power images of local residuals

For a solvable member P of the local family PSet, every homomorphism
annihilating O₂(P) maps O²(P) onto an odd prime-power group. The target
need not be the full image of P, and the conclusion keeps the literal
image subgroup under the given homomorphism.

The unique maximal subgroup of P containing the distinguished Sylow
subgroup supplies the hypotheses of Stellmacher (3.3)(a). That result
makes O²(P/O₂(P)) an odd p-group. Residual functoriality identifies it
with the image of O²(P), and factoring the given homomorphism through
P/O₂(P) proves the claim by preservation of p-groups under images.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (3.3)(a), pp.21–22.
This consequence supplies the odd residual actor on the maximal V₁
quotient in the proof of (9.1), p.47.
-/

namespace Stellmacher.SectionThree

universe u v

/-- Killing the native two-core makes the actual residual image an odd p-group. -/
public theorem pSet_residual_image_is_odd_pGroup
    {G : Type u} [Group G] [Finite G]
    {X : Type v} [Group X] [Finite X]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (f : P →* X)
    (hker : pCore 2 P ≤ f.ker) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ IsPGroup p ((twoResidualSubgroup P).map f) := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB, hSB, huniq⟩ := hP.2
  have hSP : S ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le _
  have hBnative : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    refine ⟨hB, ?_, ?_⟩
    · intro s hs
      obtain ⟨b, hb, he⟩ := hSB hs
      exact P.subtype_injective he ▸ hb
    · intro B' hB' hS'
      apply huniq B' hB'
      intro s hs
      exact ⟨⟨s, hSP hs⟩, hS' hs, rfl⟩
  obtain ⟨p, hp, hodd, hresp⟩ := (lemma_three_three S h P hP B B.normalCore hBnative
    ⟨B.normalCore_le, inferInstance, fun N hN hNB => by
      let _ := hN
      exact Subgroup.normal_le_normalCore.mpr hNB⟩ hsolv).part_a
  let π := QuotientGroup.mk' (pCore 2 P)
  let fbar := QuotientGroup.lift (pCore 2 P) f hker
  have hmap : (twoResidualSubgroup P).map π =
      twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P)) := by
    rw [twoResidualSubgroup_eq_hktPResidual', map_hktPResidual_quotient 2 (pCore 2 P)]
    exact twoResidualAmbient_top_eq_hktPResidual.symm
  refine ⟨p, hp, hodd, ?_⟩
  have himage := hresp.map fbar
  rw [← hmap, Subgroup.map_map] at himage
  exact himage

end Stellmacher.SectionThree
