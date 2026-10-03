module
public import Stellmacher.SectionEight.EightFourFixedClosureElementary
public import Stellmacher.SectionFiveToSeven.Result7_8.ElementaryGeometric
public import Stellmacher.SectionFiveToSeven.Result7_8.CoreJoinConfiguration
/-!
# The second neighboring configuration in (8.4)

Let C be the initial first-step normal closure of the faithful fixed center,
under the genuine central-first-step and nontrivial-closure branch of (8.4).
For a neighbor d of the terminal vertex, a subgroup Q in the terminal core
but outside Q_d gives the two alternatives in source (6). There is a new
neighbor m and a group L in G_d containing its conjugator and generating G_d
with its edge at m. Either L is C joined with Q_m and C intersect G_m has
index two in C, or L is Q joined with Q_m and C lies in G_m.

Source (4) puts C in the terminal core and makes it elementary abelian.
If C lies in Q_d, apply the arbitrary-core configuration to Q; the neighboring
core containment puts C inside G_m. Otherwise apply the elementary geometric
configuration to C. Both branches retain the actual transported vertex
m=act y⁻¹ a' and full-edge generation.

The selected Q in the final (8.4) consumer is O₂(O²(L0 Q_a')). Its upper
bound and noncontainment are supplied separately by the local residual-core
bound and the first residual-core noncontainment theorem. This theorem
retains precisely the two bounds it uses rather than coupling the second
configuration to the earlier extraction witnesses.
Source: Stellmacher (8.4)(6), Journal of Algebra 190 (1997), printed p.39,
`refs/files/stellmacher-n-group.pdf`; C is the initial Vstar_(a+1).

The local theorem uses only the stated Section Eight local hypotheses and
preserves all selected witnesses. The original canonical API is an exact
wrapper through the same graph.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
public theorem eight_four_second_configuration_local
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
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (d : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d ctx.criticalPath.a')
    (Q : Subgroup H) (hQ : Q ≤ QAt ctx.Γ ctx.criticalPath.a')
    (hQnot : ¬ Q ≤ QAt ctx.Γ d) :
    let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    ∃ y : H, ∃ L : Subgroup H,
      y ∈ L ∧ L ≤ GAt ctx.Γ d ∧
      ctx.Γ.adjacent d (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
      L ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) = GAt ctx.Γ d ∧
      ((L = C ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
        Nat.card C = 2 * Nat.card ↥(C ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) ∨
       (L = Q ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
        C ≤ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) := by
  classical
  let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
  change ∃ y : H, ∃ L : Subgroup H, _
  have hC : C ≤ QAt ctx.Γ ctx.criticalPath.a' :=
    (eight_four_fixed_closure_control_local ctx hcenter w hbranch).1
  have hElem : IsElementaryAbelian 2 C :=
    eight_four_fixed_closure_elementary_local ctx hcenter w hbranch
  let h := ctx.sectionSeven
  have hl : ctx.criticalPath.a' ∈ neighborhood ctx.Γ d :=
    (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mpr hadj
  by_cases hCd : C ≤ q ctx.Γ d
  · obtain ⟨y,hy,hLP,hm,hgen⟩ :=
      sevenEight_core_join_configuration h ctx.Γ d ctx.criticalPath.a' hl Q hQ hQnot
    have hm' := (SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mp hm
    have hCore : q ctx.Γ d ≤ stabilizer ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a') :=
      ((lemma_seven_three h ctx.Γ).sylow_and_core d _ hm default).2.2
    exact ⟨y,_,hy,hLP,hm',hgen,Or.inr ⟨rfl,hCd.trans hCore⟩⟩
  · obtain ⟨y,hy,hLP,hm,hgen,hcard⟩ :=
      sevenEight_elementary_geometric_configuration h ctx.Γ d ctx.criticalPath.a' hl C hC hCd hElem
    exact ⟨y,_,hy,hLP,(SevenSix.mem_neighborhood_iff_adjacent ctx.Γ).mp hm,
      hgen,Or.inl ⟨rfl,hcard⟩⟩

/-- Canonical specialization through the same graph and quotient witness. -/
public theorem eight_four_second_configuration
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
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (d : ctx.Γ.Vertex) (hadj : ctx.Γ.adjacent d ctx.criticalPath.a')
    (Q : Subgroup H) (hQ : Q ≤ QAt ctx.Γ ctx.criticalPath.a')
    (hQnot : ¬ Q ≤ QAt ctx.Γ d) :
    let C := (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype
    ∃ y : H, ∃ L : Subgroup H,
      y ∈ L ∧ L ≤ GAt ctx.Γ d ∧
      ctx.Γ.adjacent d (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
      L ⊔ (GAt ctx.Γ d ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a')) = GAt ctx.Γ d ∧
      ((L = C ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
        Nat.card C = 2 * Nat.card ↥(C ⊓ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) ∨
       (L = Q ⊔ QAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a') ∧
        C ≤ GAt ctx.Γ (ctx.Γ.act y⁻¹ ctx.criticalPath.a'))) := by
  exact eight_four_second_configuration_local ctx.toLocalContext hcenter w hbranch d hadj Q hQ hQnot

end Stellmacher.SectionEight
