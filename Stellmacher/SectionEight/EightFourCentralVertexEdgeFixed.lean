module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.EightFourEdgeFixedTransport

/-!
# A central vertex center lies in the edge-fixed subgroup

For the exact transported family F of a graph-local central-first-step
context, every
ordered edge (d,l) whose second center is central in G_l has Z_l≤F(d,l).
The family is supplied with its original base value and covariance; no later
fixed-subgroup normality or nontrivial-closure assumption is used. The local
theorem keeps the original witness, family, base equation, covariance, and
ordered edge. The original canonical theorem is an exact wrapper through
`ctx.toLocalContext`, and its prior import and reexports are retained.

At the initial edge, the Sylow omega-center is contained in the central
first-step center and is therefore normal in its stabilizer. Its defining
conjugate join then equals that first-step center. Hence the center lies
in the initial module and centralizes the edge Sylow. The exact quotient
witness and J's containment in the Sylow image put it in the J-fixed subgroup.
Edge transitivity transports this inclusion. Reversed orientation would
send the initial center to the central endpoint; the transported opposite
center lies in that stabilizer by (7.4), contradicting endpoint noncommutation.

This supplies the reverse inclusion in source (9) of Stellmacher (8.4),
Journal of Algebra190 (1997), printed p40, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
private theorem first_center_le_fixed
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    ZAt ctx.Γ ctx.criticalPath.firstStep ≤ w.oneJFixedPoints S := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Pb := GAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let h := ctx.sectionSeven
  have hSyl := SevenSix.edge_sylow_data h Γ cp
  have homega (d : Γ.Vertex) (hd : IsSylowTwoIn S (GAt Γ d)) :
      omegaOneCenter S ≤ ZAt Γ d := by
    obtain ⟨_,T,hT⟩ := hd
    rw [ZAt,z,Γ.zAt_def]
    exact le_sSup ⟨T,congrArg omegaOneCenter hT.symm⟩
  have hOmegaC : omegaOneCenter S ≤ CenterAmbient Pb := (homega _ hSyl.2).trans hcenter
  have hOmegaP : omegaOneCenter S ≤ Pb := hOmegaC.trans (Subgroup.map_subtype_le _)
  have hn : NormalIn (omegaOneCenter S) Pb := by
    refine ⟨hOmegaP,(Subgroup.normal_subgroupOf_iff_le_normalizer hOmegaP).mpr ?_⟩
    apply (Subgroup.centralizer_le_normalizer (omegaOneCenter S : Set H)).trans'
    apply Subgroup.le_centralizer_iff.mpr
    exact hOmegaC.trans (SevenSix.centerAmbient_le_centralizer Pb)
  have hz : ZAt Γ cp.firstStep = omegaOneCenter S :=
    z_eq_omega_sylow_of_normal Γ cp.firstStep hSyl.2 hn
  have hZbZa : ZAt Γ cp.firstStep ≤ Za := hz.le.trans (homega _ hSyl.1)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := Za) Sb
  have hJS : J ≤ Sb := sSup_le fun A hA => hA.1
  have hfix : ZAt Γ cp.firstStep ≤ Za ⊓ Subgroup.centralizer (S : Set H) :=
    le_inf hZbZa (hcenter.trans ((SevenSix.centerAmbient_le_centralizer Pb).trans
      (Subgroup.centralizer_le hSyl.2.1)))
  intro z hz
  obtain ⟨v,hv,hvz⟩ := (w.fixedPoints_map_subtype S hSyl.1.1).symm ▸ (hfix hz)
  refine ⟨v,?_,hvz⟩
  intro j
  exact hv ⟨j,hJS j.property⟩
/-- A central second endpoint center lies in the actual transported edge-fixed subgroup. -/
public theorem eight_four_central_vertex_le_edge_fixed_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (d l : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d l)
    (hcentral : ZAt ctx.Γ l ≤ CenterAmbient (GAt ctx.Γ l)) :
    ZAt ctx.Γ l ≤ F d l := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  obtain ⟨g,hg⟩ := (lemma_seven_one h Γ).edge_not_vertex_transitive.1 cp.firstStep_adj hadj
  rcases hg with hok | hbad
  · have hF := hcov g cp.a cp.firstStep
    rw [hok.1,hok.2,hbase] at hF
    rw [hF]
    change z Γ l ≤ (w.oneJFixedPoints S).conjBy g⁻¹
    have hZ := z_act Γ g cp.firstStep
    rw [hok.2] at hZ
    rw [hZ]
    exact Subgroup.map_mono (first_center_le_fixed ctx hcenter w)
  · have hZendP : z Γ (Γ.act g cp.a') ≤ stabilizer Γ l := by
      rw [← hbad.1,stabilizer_act,z_act]
      exact Subgroup.map_mono (lemma_seven_four h Γ cp).reverse_containment.1
    have hc : ⁅z Γ l,z Γ (Γ.act g cp.a')⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (hcentral.trans ((SevenSix.centerAmbient_le_centralizer _).trans
          (Subgroup.centralizer_le hZendP)))
    rw [← hbad.1,z_act,z_act,← Subgroup.map_commutator] at hc
    exact (ctx.commutator_ne (Subgroup.map_injective (MulAut.conj g⁻¹).injective
      (hc.trans (Subgroup.map_bot _).symm))).elim

/-- The canonical context retains the exact supplied family and covariance. -/
public theorem eight_four_central_vertex_le_edge_fixed
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (F : ctx.Γ.Vertex → ctx.Γ.Vertex → Subgroup H)
    (hbase : F ctx.criticalPath.a ctx.criticalPath.firstStep = w.oneJFixedPoints S)
    (hcov : ∀ g d l, F (ctx.Γ.act g d) (ctx.Γ.act g l) = (F d l).conjBy g⁻¹)
    (d l : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d l)
    (hcentral : ZAt ctx.Γ l ≤ CenterAmbient (GAt ctx.Γ l)) :
    ZAt ctx.Γ l ≤ F d l := by
  exact eight_four_central_vertex_le_edge_fixed_local ctx.toLocalContext hcenter w F hbase hcov d l hadj hcentral

end Stellmacher.SectionEight
