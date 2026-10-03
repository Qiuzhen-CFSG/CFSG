module
public import Stellmacher.SectionNine.NineFourNoncentralAuxiliary
public import Stellmacher.SectionNine.NineFourCentralAuxiliary

/-!
# Stellmacher (9.4): containment of the local subgroup

The original commutator, generation, and quotient-cardinality hypotheses
force A into the next vertex module. The ambient theorem applies directly
to an embedded local context, and the original public theorem remains its
canonical-context specialization with the same hypotheses.

Assuming a counterexample, the normalization theorem conjugates all of its
data together and enlarges A by the neighboring module intersection. It
preserves the three original hypotheses and supplies the source-(4) index
bound. For the literal auxiliary residual core, either some auxiliary
commutator module is larger than the next center or all are equal to that
center. The separate noncentral and central arguments exclude these two
cases. In particular, neither factor normalization nor a fixed-subgroup
identity is assumed by this assembly.

Source: Stellmacher, (9.4), printed pp.50–52 / PDF pp.40–42 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- Ambient form of Stellmacher (9.4), preserving the supplied actor,
conjugator, and three local hypotheses. -/
public theorem lemma_nine_four_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (r : ctx.Γ.Vertex)
    (hr : ctx.Γ.distance r ctx.criticalPath.firstStep = 2)
    (t : G)
    (ht : t ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∈ Subgroup.centralizer (VAt ctx.Γ r : Set G))
    (x : G)
    (hx : x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆)
    (A : Subgroup G)
    (hA : A ≤ VAt ctx.Γ (ctx.Γ.act x r))
    (h1 : ⁅A, Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (h2 : ∀ n : ctx.Γ.Vertex,
      n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      n ∈ Neighborhood ctx.Γ (ctx.Γ.act x r) →
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
        Subgroup.zpowers t = GAt ctx.Γ ctx.criticalPath.firstStep)
    (h3 : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) 2) :
    A ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  by_contra hnot
  let data : NineFourCounterexample ctx := {
    remote := r
    distance := hr
    actor := t
    actor_mem := ht.1
    actor_centralizes := ht.2
    conjugator := x
    conjugator_mem := hx
    subgroup := A
    subgroup_le := hA
    commutator_le := h1
    generates := h2
    displacement := h3
    not_le := hnot }
  obtain ⟨normalized, hneighbor, hdistinct, hintersection, hindex⟩ :=
    nine_four_normalized_enlarged_counterexample ctx hb data
  let F := (QAt ctx.Γ ctx.criticalPath.a ⊓
    QAt ctx.Γ (ctx.Γ.act normalized.conjugator normalized.remote)) ⊔
      Subgroup.zpowers normalized.actor
  let Q := twoCoreIn (twoResidualIn F)
  by_cases hnoncentral : ∃ y ∈ normalized.subgroup,
    ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,Q⁆ ⊔
      ZAt ctx.Γ ctx.criticalPath.firstStep ≠ ZAt ctx.Γ ctx.criticalPath.firstStep
  · exact nine_four_noncentral_auxiliary_false ctx hb normalized hneighbor hdistinct
      hindex hnoncentral
  · apply nine_four_central_auxiliary_false ctx hb normalized hneighbor hdistinct
      hintersection hindex
    intro y hy
    exact not_ne_iff.mp (fun hne => hnoncentral ⟨y,hy,hne⟩)

/-- **Stellmacher (9.4).**  The local subgroup `A` is forced into
`V_{a+1}` by the three displayed commutator, generation, and index
hypotheses. -/
public theorem lemma_nine_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (r : ctx.Γ.Vertex)
    (hr : ctx.Γ.distance r ctx.criticalPath.firstStep = 2)
    (t : H)
    (ht : t ∈ GAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∈ Subgroup.centralizer (VAt ctx.Γ r : Set H))
    (x : H)
    (hx : x ∈ ⁅EAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆)
    (A : Subgroup H)
    (hA : A ≤ VAt ctx.Γ (ctx.Γ.act x r))
    (h1 : ⁅A, Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ ctx.criticalPath.firstStep)
    (h2 : ∀ n : ctx.Γ.Vertex,
      n ∈ Neighborhood ctx.Γ ctx.criticalPath.firstStep →
      n ∈ Neighborhood ctx.Γ (ctx.Γ.act x r) →
      (GAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ n) ⊔
        Subgroup.zpowers t = GAt ctx.Γ ctx.criticalPath.firstStep)
    (h3 : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.firstStep, Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep)
      (ZAt ctx.Γ ctx.criticalPath.firstStep) 2) :
    A ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  exact lemma_nine_four_ambient ctx.toAmbientContext hb r hr t ht x hx A hA h1 h2 h3


end Stellmacher.SectionNine
