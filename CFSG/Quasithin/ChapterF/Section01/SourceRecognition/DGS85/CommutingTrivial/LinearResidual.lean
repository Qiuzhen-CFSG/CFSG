module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingTrivial.NeighborSylow
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.QuotientFaithfulness

/-!
# Corrected 5.12 premises on the literal commuting residual section

Assume the literal residual-section action descends through a supplied actual
SL₂ quotient of the intrinsic beta local group. The neighboring-core image
is then the actual Sylow, its fixed space generates the same section, the
residual fixed space is zero, and the action is faithful. The opposite
radius-one span remains the literal quadratic actor, including field two.

The source 6.5(a) normality obstruction is used only to prove neighboring-core
escape; its producer is qt-dgs85-setup-obstruction. Constructing the action
descent, recognizing the local quotient, and applying the strict numerical
comparison remain with the Chapter 9 owner. The quotient is not recognized
by this conditional preparation theorem.

Source: DGS, *Groups and Graphs* (1985), 5.12 and 9.3, printed pp.113--114
and 142; published fixed-space-generation correction to 5.12.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition Representation.NormalElementaryQuotient
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
/-- On the constructed V_beta/C_V_beta(O²(L_beta)), the exact 6.5(a) premise
and supplied linear quotient action discharge generation and faithfulness.
No Sylow-fixed generation or faithful-action premise is assumed. -/
theorem reduced_critical_linear_residual_prepared (h : HypothesisF11 L S₀)
    {a beta a' : Vertex (Reduction.reducedFamily L S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily L S₀) a a')
    (hab : (graph (Reduction.reducedFamily L S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily L S₀)).dist beta a' + 1 = b (Reduction.reducedFamily L S₀))
    (hb : 1 < b (Reduction.reducedFamily L S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily L S₀) a, Z (Reduction.reducedFamily L S₀) a'⁆ = ⊥)
    (hob : ¬ stabilizer (Reduction.reducedFamily L S₀) a ≤ normalizer
      ((Q (Reduction.reducedFamily L S₀) beta ⊓ Q (Reduction.reducedFamily L S₀) a :
        Subgroup (Reduction.G₀ L S₀)) : Set (Reduction.G₀ L S₀)))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2^n)
    (e : (graphLocalGroup (Reduction.reducedFamily L S₀) beta ⧸
      pCore 2 (graphLocalGroup (Reduction.reducedFamily L S₀) beta)) ≃* SL(2,F)) :
    let Γ := Reduction.reducedFamily L S₀
    let H := graphLocalGroup Γ beta
    let A := (V Γ beta 1).subgroupOf H
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
    letI : ∀ i, Finite (Γ i) := finite_endpoints (Reduction.reduced_triple h)
    letI := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
    ∀ hb2 : 2 < b Γ,
      letI := neighborhoodIn_elementary Γ (Reduction.reduced_triple h).generate
        (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
        (Reduction.reduced_kernel_sylow h) beta hb2 H
      ∀ σ : Representation (ZMod 2) SL(2,F) (FixedQuotient A (pResidual 2 H)),
        (∀ l : H, σ (q l) = fixedQuotientAction A (pResidual 2 H) l) →
        ∃ T : Sylow 2 SL(2,F), ((Q Γ a).subgroupOf H).map q = T ∧
          GeneratedByFixedSpace σ T ∧
          fixedSpace σ (pResidual 2 SL(2,F)) = ⊥ ∧ Function.Injective σ ∧
          IsQuadratic σ (((V Γ a' 1).subgroupOf H).map q) ∧
          ∀ l : H, q l ∈ normalizer (T : Set SL(2,F)) ↔ (l : Reduction.G₀ L S₀) • a = a := by
  let ht := Reduction.reduced_triple h
  let Γ := Reduction.reducedFamily L S₀
  let H := graphLocalGroup Γ beta
  let A := (V Γ beta 1).subgroupOf H
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  let : ∀ i, Finite (Γ i) := finite_endpoints ht
  let := neighborhoodIn_normal Γ beta H (sylowGenerated_le _)
  dsimp only
  intro hb2
  let := neighborhoodIn_elementary Γ ht.generate (fun v => (source_Z_Q_U ht v).1)
    (Reduction.reduced_kernel_sylow h) beta hb2 H
  intro σ hact
  obtain ⟨_, hnz, ⟨c⟩, hr, _, hquad⟩ := reduced_critical_residual_section h hc hab hd hb hcomm
  let : Nontrivial (FixedQuotient A (pResidual 2 H)) := hnz
  let : Finite H := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hcomp : σ.comp q = fixedQuotientAction A (pResidual 2 H) := MonoidHom.ext hact
  have hr' : fixedSpace σ (pResidual 2 SL(2,F)) = ⊥ := by
    rw [← map_pResidual_of_surjective 2 q hq, ← fixedSpace_comp_map, hcomp]
    exact hr
  have hne := core_escape_of_intersection_obstruction Γ hob
  obtain ⟨T, hT, hg, hTf⟩ := linear_residual_section_sylow_generation ht
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hab.symm hne (Reduction.reduced_commuting_critical_geometry h hc hab hd hb hcomm).2.2.1
    e σ (hcomp.symm ▸ c)
  refine ⟨T, hT, hg, hr', CommutingNontrivial.linear_quotient_action_faithful hn hF e σ hr', ?_, hTf⟩
  rw [← hcomp] at hquad
  rintro x ⟨x', hx, rfl⟩ y ⟨y', hy, rfl⟩ z
  exact hquad x' hx y' hy z
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
