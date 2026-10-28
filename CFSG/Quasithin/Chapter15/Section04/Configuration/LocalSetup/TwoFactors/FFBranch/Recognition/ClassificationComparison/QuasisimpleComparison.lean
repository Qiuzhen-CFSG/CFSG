module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.Prepared
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SymmetricThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.SylowBound
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.Targets
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.ActorPruning
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison.AmbientExtensions
/-!
# The quasisimple part of the mixed FF comparison

`ProjectiveLine.ClassifiedAction.compared_branch` proves the quasisimple
branch of the F.6.18/B.5.6 comparison on the actual offender subgroup N.
The ambient Sylow bound first gives the bounded actor catalogue. Actor
pruning intersects it with all twelve retained Goldschmidt rows, in either
orientation. The ambient comparison then resolves the two-group quotient
D/N using the actual field and graph actions. Row (1) was already excluded
by the Goldschmidt preparation from the different embedded local cores.

The result retains L₃(2), A₆, S₆, A₇, S₇, the perfect triple-six cover,
G₂(2)′ and G₂(2); the ambient group additionally permits the triple-symmetric
six cover. Every ordinary model comes with an actual equivalence, and both
covers keep their covering maps. The marked offender, component, residual,
quotient, derived subgroup and centralizer use the original inclusions.
The transported action restricts to precisely the original action on N.

`ComparedBranch` retains all six corrected B.5.1 module clauses, and its
constructor preserves the exact supplied source conclusion. In particular
the triple-six offender fixes a two-dimensional F₄ subspace, as in K.1.3.
Neither N = D nor a three-rank bound is assumed. The quotient application
uses the literal H/O₂(H) representation and offender action of 15.4.18.
The parent comparison retains the exhaustive disjunction over all FF
branches; subsequent module exclusions and S₃ × S₃ recognition are separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 15.4.18,
p.1163; F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; K.1.3, p.453.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v

namespace QuasisimpleComparison

/-- The proved smaller actor and marked ambient models, together with the
complete source action on the literal offender subgroup. This is an output
of the comparison, not an additional classification hypothesis. -/
structure ComparedBranch {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) extends
    BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype) where
  smallActor : SmallActorModel (offenderSubgroup ρ)
  ambient : AmbientExtensions.MarkedSmallAmbientModel ρ

end QuasisimpleComparison
open QuasisimpleComparison

variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}

/-- Complete the quasisimple comparison, discharging both the bounded-model
and small-actor premises. The equality preserves the supplied module data,
including every nonsplit and extension clause, on the original action. -/
theorem ProjectiveLine.ClassifiedAction.compared_branch
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    ∃ b : ComparedBranch ρ, b.source = c := by
  obtain ⟨hm, ha⟩ := h.bounded_quasisimple hq c
  let b : BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype) := ⟨hq, c, hm, ha⟩
  have hs := h.smallActor_of_bounded b
  exact ⟨⟨b, hs, AmbientExtensions.comparison_marked h b hs⟩, rfl⟩

/-- The reduced group alternatives retain all original subgroup and action
markings, without identifying the offender actor with its ambient group. -/
theorem ProjectiveLine.ClassifiedAction.quasisimple_comparison
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    SmallActorModel (offenderSubgroup ρ) ∧ AmbientExtensions.MarkedSmallAmbientModel ρ := by
  obtain ⟨b, _⟩ := h.compared_branch hq c
  exact ⟨b.smallActor, b.ambient⟩

/-- Forget only the markings from the proved ambient classification. -/
theorem ProjectiveLine.ClassifiedAction.smallAmbient_of_quasisimple_source
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂)
    (hq : IsQuasisimple (generalizedFitting (offenderSubgroup ρ)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (generalizedFitting (offenderSubgroup ρ))) :
    SmallAmbientModel D :=
  (h.quasisimple_comparison hq c).2.smallAmbientModel

/-- Apply the comparison to the literal quotient and offender action used
in 15.4.18. The earlier preparation supplies `h`; no new universal classifier,
model bound, small-actor premise or ambient-equals-offender premise is needed. -/
theorem ProjectiveLine.quasisimple_comparison_on_quotient
    {H : Type u} [Group H] [Finite H] {K : GroupClass.{u}}
    (G₁ G₂ : Subgroup H) (P : Sylow 2 H) (Z : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (h : ProjectiveLine.ClassifiedAction K (quotientAction P Z hC)
      (G₁.map coreProjection) (G₂.map coreProjection))
    (hq : IsQuasisimple (generalizedFitting (offenderGroup P Z hC)))
    (c : FFAlternatives.ProjectiveLine.QuasisimpleSourceConclusion
      (offenderAction P Z hC) (generalizedFitting (offenderGroup P Z hC))) :
    ∃ b : ComparedBranch (quotientAction P Z hC), b.source = c :=
  h.compared_branch hq c

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
