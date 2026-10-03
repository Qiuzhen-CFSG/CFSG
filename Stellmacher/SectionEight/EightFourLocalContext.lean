module

public import Stellmacher.SectionEight.EightFourCentralizerCriterion
public import Stellmacher.SectionEight.LemmaEightThree
public import Stellmacher.SectionEight.GeneratedEightThree
public import Stellmacher.SectionEight.GeneratedEightFiveVectorCriterion

/-!
# Ambient inputs for the local proof of (8.4)

The local graph proof uses exactly two consequences of Hypothesis Two: the
(8.3) residual-core noncontainment and the (6.4) fixed-vector centralizer
criterion. The context retains these conclusions for every noncommuting
critical path in the same graph, so changing a critical endpoint preserves
the actual witnesses and the two proved ambient inputs.

The canonical and generated adapters apply the existing proved results to
that literal path and graph. In the generated adapter Hypothesis Two stays
on the original ambient group. Neither callback assumes fixed-subgroup
normality, and no inheritance of Hypothesis Two to the generated subgroup
is used. The adapters sit above the pure local opposite-closure foundation
and feed the remaining (8.4) closure and transported-edge arguments.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.3) and (8.4), printed
pp.38–40, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

public structure EightFourLocalContext
    (H : Type u) [Group H] [Finite H] (S P1 P2 : Subgroup H)
    extends SectionEightLocalContext H S P1 P2 where
  core_noncontainment : ∀ cp : CriticalPath Γ,
    ⁅Γ.z cp.a, Γ.z cp.a'⁆ ≠ ⊥ →
    ZAt Γ cp.firstStep ≤ CenterAmbient (GAt Γ cp.firstStep) →
    ¬ twoCoreIn (EAt Γ cp.a) ≤ QAt Γ cp.firstStep
  vector_criterion : ∀ cp : CriticalPath Γ,
    ⁅Γ.z cp.a, Γ.z cp.a'⁆ ≠ ⊥ →
    ZAt Γ cp.firstStep ≤ CenterAmbient (GAt Γ cp.firstStep) →
    ∀ w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set H)) (ZAt Γ cp.a),
    ∀ v : H, v ∈ w.oneJFixedPoints S →
    (GAt Γ cp.firstStep ⊓ Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = GAt Γ cp.firstStep →
    v ∈ ZAt Γ cp.firstStep

@[expose] public def EightFourLocalContext.toLocalContext
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2) : SectionEightLocalContext H S P1 P2 :=
  ctx.toSectionEightLocalContext

@[expose] public def EightFourLocalContext.withCriticalPath
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (cp : CriticalPath ctx.Γ) (hcomm : ⁅ctx.Γ.z cp.a, ctx.Γ.z cp.a'⁆ ≠ ⊥) :
    EightFourLocalContext H S P1 P2 where
  toSectionEightLocalContext := { ctx.toSectionEightLocalContext with
    criticalPath := cp
    commutator_ne := hcomm }
  core_noncontainment := ctx.core_noncontainment
  vector_criterion := ctx.vector_criterion

@[expose] public def _root_.Stellmacher.Later.SectionEightContext.toEightFourContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2) : EightFourLocalContext H S P1 P2 where
  toSectionEightLocalContext := ctx.toLocalContext
  core_noncontainment cp hcomm hcenter :=
    lemma_eight_three { ctx with criticalPath := cp, commutator_ne := hcomm } hcenter
  vector_criterion cp hcomm hcenter :=
    eight_four_vector_centralizer_criterion
      { ctx with criticalPath := cp, commutator_ne := hcomm } hcenter

@[expose] public def _root_.Stellmacher.Later.GeneratedSectionEightContext.toEightFourContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : GeneratedSectionEightContext H S0 S P1 P2) :
    EightFourLocalContext (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2)) where
  toSectionEightLocalContext := ctx.toLocalContext
  core_noncontainment cp hcomm hcenter :=
    generated_lemma_eight_three
      { ctx with criticalPath := cp, commutator_ne := hcomm } hcenter
  vector_criterion cp hcomm hcenter :=
    generated_eight_four_vector_centralizer_criterion
      { ctx with criticalPath := cp, commutator_ne := hcomm } hcenter

public theorem lemma_eight_three_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep)) :
    ¬ twoCoreIn (EAt ctx.Γ ctx.criticalPath.a) ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
  ctx.core_noncontainment ctx.criticalPath ctx.commutator_ne hcenter

public theorem eight_four_vector_centralizer_criterion_local
    {H : Type u} [Group H] [Finite H] {S P1 P2 : Subgroup H}
    (ctx : EightFourLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (v : H) (hv : v ∈ w.oneJFixedPoints S)
    (hgen : (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      Subgroup.centralizer ({v} : Set H)) ⊔
      (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
        GAt ctx.Γ ctx.criticalPath.firstStep) :
    v ∈ ZAt ctx.Γ ctx.criticalPath.firstStep :=
  ctx.vector_criterion ctx.criticalPath ctx.commutator_ne hcenter w v hv hgen

end Stellmacher.SectionEight
