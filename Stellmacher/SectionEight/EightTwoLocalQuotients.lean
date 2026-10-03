module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result6_3
public import Stellmacher.SectionFiveToSeven.Result7_1
public import Stellmacher.SectionEight.NoncentralSylowCenterAction
public import Stellmacher.SectionEight.LocalQuotientSL2

/-!
# Local quotients in the noncentral branch of (8.2)

The actual dihedral core-quotient conclusion is also supplied over the
ambient-retaining local context. Its conditional (6.3) pair and genuine
Section Seven hypotheses suffice, with no ambient Sylow parameter. The
legacy theorem retains its faithful center-action conclusion and signature.

For the actual Section Eight critical-pair context, assume the first-step
vertex center is not central in its stabilizer. Every vertex stabilizer
then has an ordinary dihedral two-core quotient with rotation order a
power of three. Every exact center-action quotient witness at the initial
critical vertex has quotient group SL2(2).

The noncentral Sylow-center theorem supplies the hypotheses of (6.3).
The two base dihedral quotient isomorphisms are transported to all vertices
using (7.1)'s actual stabilizer conjugacy and functoriality of the two-core.
At the initial critical vertex, the existing faithful-quotient bridge
uses the original witness projection and its opposite-endpoint offender
to identify the center-action quotient with SL2(2).

Source: Stellmacher (8.2), opening paragraph, Journal of Algebra 190
(1997), p.37, refs/latex/stellmacher-n-group.tex. Neither critical distance
one nor the eventual whole-stabilizer classification is assumed here.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven
universe u

private theorem dihedral_core_of_equiv
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H)
    (h : ∃ n : ℕ, Nonempty ((G ⧸ pCore 2 G) ≃* DihedralGroup (3 ^ n))) :
    ∃ n : ℕ, Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup (3 ^ n)) := by
  obtain ⟨n, ⟨eD⟩⟩ := h
  let eQ := QuotientGroup.congr (pCore 2 G) (pCore 2 H) e (pCore_map_iso 2 e)
  exact ⟨n, ⟨eQ.symm.trans eD⟩⟩

public theorem eight_two_dihedral_core_local
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ∀ d : ctx.Γ.Vertex, ∃ n : ℕ,
      Nonempty ((GAt ctx.Γ d ⧸ pCore 2 (GAt ctx.Γ d)) ≃* DihedralGroup (3 ^ n)) := by
  obtain ⟨_hleft, hright⟩ := eight_two_noncentral_sylow_center_action_local ctx hcenter
  obtain ⟨hP1, hP2⟩ := ctx.sixThree.dihedralCore hright
  intro d
  obtain ⟨element, hd | hd⟩ :=
    (lemma_seven_one ctx.sectionSeven ctx.Γ).vertex_stabilizers_conjugate d
  · change ∃ n : ℕ, Nonempty ((ctx.Γ.stabilizer d ⧸ pCore 2 (ctx.Γ.stabilizer d)) ≃*
      DihedralGroup (3 ^ n))
    rw [hd]
    exact dihedral_core_of_equiv ((MulAut.conj element).subgroupMap P1) hP1
  · change ∃ n : ℕ, Nonempty ((ctx.Γ.stabilizer d ⧸ pCore 2 (ctx.Γ.stabilizer d)) ≃*
      DihedralGroup (3 ^ n))
    rw [hd]
    exact dihedral_core_of_equiv ((MulAut.conj element).subgroupMap P2) hP2

public theorem eight_two_local_quotients
    {G : Type u} [Group G] [Finite G]
    {S0 : Sylow 2 G} {S P1 P2 : Subgroup G}
    (ctx : SectionEightContext G S0 S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    (∀ d : ctx.Γ.Vertex, ∃ n : ℕ,
      Nonempty ((GAt ctx.Γ d ⧸ pCore 2 (GAt ctx.Γ d)) ≃* DihedralGroup (3 ^ n))) ∧
    (∀ w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a),
      let _ := w.groupX
      let _ := w.finiteX
      IsSL2Two w.X) := by
  have hall := eight_two_dihedral_core_local ctx.toLocalContext hcenter
  refine ⟨hall, ?_⟩
  intro w
  obtain ⟨n, ⟨eD⟩⟩ := hall ctx.criticalPath.a
  exact local_quotient_isSL2Two_of_dihedral_core ctx w n eD

end Stellmacher.SectionEight
