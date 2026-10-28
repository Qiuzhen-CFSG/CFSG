module
public import Stellmacher.SectionThree.LemmaThreeThree
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Odd residual in a local group's core quotient

Let a finite solvable group satisfy the Section Three hypotheses at S,
with the whole group in the associated local family. For any surjection
q onto X whose kernel is exactly the two-core, the two-residual of X has
odd order.

Apply Stellmacher (3.3)(a) to the native top subgroup and its unique
maximal overgroup of S. Its ordinary two-core quotient has an odd-prime
two-residual. The top-subgroup equivalence and the quotient equivalence
induced by q transport that residual to the literal two-residual in X.
Its odd-prime-power cardinality is therefore odd.

This is the source-neutral local-group consequence used in Stellmacher
(8.3), Journal of Algebra 190 (1997), p38; its input is (3.3), pp21--22.
Source: refs/latex/stellmacher-n-group.tex. No action quotient or graph
hypothesis is substituted for the stated ordinary two-core quotient.
-/

namespace Stellmacher.SectionThree
universe u v

/-- The two-residual of an ordinary local two-core quotient has odd order. -/
public theorem odd_card_twoResidual_of_core_quotient
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (h : Hypotheses G S)
    (hP : (⊤ : Subgroup G) ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable G)
    {X : Type v} [Group X] [Finite X]
    (q : G →* X) (hq : Function.Surjective q) (hker : q.ker = pCore 2 G) :
    Odd (Nat.card (twoResidualAmbient (⊤ : Subgroup X))) := by
  let P : Subgroup G := ⊤
  obtain ⟨B, hB, hSB, huniq⟩ := hP.2
  have hBnative : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    refine ⟨hB, ?_, ?_⟩
    · intro s hs
      obtain ⟨b, hb, he⟩ := hSB hs
      exact P.subtype_injective he ▸ hb
    · intro B' hB' hS'
      apply huniq B' hB'
      intro s hs
      exact ⟨⟨s, trivial⟩, hS' hs, rfl⟩
  have hPsolv : Group.IsSolvable P := by
    let _ := hsolv
    infer_instance
  obtain ⟨p, hp, hodd, hresp⟩ := (lemma_three_three S h P hP B B.normalCore hBnative
    ⟨B.normalCore_le, inferInstance, fun N hN hNB => by
      let _ := hN
      exact Subgroup.normal_le_normalCore.mpr hNB⟩ hPsolv).part_a
  let eP : P ≃* G := Subgroup.topEquiv
  let eCore : (P ⧸ pCore 2 P) ≃* (G ⧸ pCore 2 G) :=
    QuotientGroup.congr _ _ eP (pCore_map_iso 2 eP)
  let eX : (G ⧸ pCore 2 G) ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let e := eCore.trans eX
  have hmap : (twoResidualAmbient (⊤ : Subgroup (P ⧸ pCore 2 P))).map e.toMonoidHom =
      twoResidualAmbient (⊤ : Subgroup X) :=
    map_twoResidualAmbient_of_subgroup_image ⊤ e.toMonoidHom ⊤
      (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective)
  have hpX : IsPGroup p (twoResidualAmbient (⊤ : Subgroup X)) := by
    rw [← hmap]
    exact hresp.map e.toMonoidHom
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpX.exists_card_eq
  rw [hn]
  exact hodd.pow

end Stellmacher.SectionThree

