module

public import Stellmacher.SectionNine.NineTenNormalizedResidualWitnesses

/-!
# Normalized second-extraction interfaces in (9.10)

These statement-preserving adapters expose the established normalized
second-extraction interfaces. The common producer transports both actual
extractions and the supplied path by one automorphism. The strongest
interface here keeps the prescribed actor's residual commutator bound;
the older interfaces respectively retain the terminal neighbor or just
the second geometric data and its normalized initial-vertex identity.

The richer first residual witness is available directly from
`NineTenNormalizedResidualWitnesses` for the selected-support proof.
Source: Stellmacher (9.10), printed p.57, normalization before assertion (2).
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_normalized_extraction_with_actor_commutator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        neighbor ∈ neighborhood ctx.Γ cp.a' ∧
        actor ∈ ZAt ctx.Γ neighbor ∧
        ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ ∧
        twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆ := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, neighbor, second, actor,
    E, A0, data, hsecond, hnew, hneighbor, hactor, hnoncomm, hactorComm, _⟩ :=
    nine_ten_normalized_extraction_with_residual_witnesses ctx hb hterminalNot hfirstNot
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, neighbor, second, actor,
    E, A0, data, hsecond, hnew, hneighbor, hactor, hnoncomm, hactorComm⟩

/-- The original normalized interface retaining the terminal neighbor. -/
public theorem nine_ten_normalized_extraction_with_neighbor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a ∧
        neighbor ∈ neighborhood ctx.Γ cp.a' ∧
        actor ∈ ZAt ctx.Γ neighbor ∧
        ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥ := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, neighbor, second, actor,
    E, A0, data, hsecond, hnew, hneighbor, hactor, hnoncomm, _⟩ :=
    nine_ten_normalized_extraction_with_actor_commutator ctx hb hterminalNot hfirstNot
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, neighbor, second, actor,
    E, A0, data, hsecond, hnew, hneighbor, hactor, hnoncomm⟩

/-- The original normalized extraction interface. -/
public theorem nine_ten_normalized_extraction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a') :
    ∃ cp : CriticalPath ctx.Γ,
      cp.length = ctx.criticalPath.length ∧
      ⁅ZAt ctx.Γ cp.a, ZAt ctx.Γ cp.a'⁆ = ⊥ ∧
      (¬ ZAt ctx.Γ cp.a' ≤ VAt ctx.Γ cp.firstStep) ∧
      (¬ ZAt ctx.Γ cp.firstStep ≤ VAt ctx.Γ cp.a') ∧
      ∃ (second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
        (data : NineThreeGeometricData ctx.Γ cp.firstStep second
          (VAt ctx.Γ cp.a') E A0 actor),
        IsCriticalPathOffset ctx.Γ cp 2 second ∧
        ctx.Γ.act data.x⁻¹ second = cp.a := by
  obtain ⟨cp, hlength, hcomm, hterminal, hfirst, _, second, actor, E, A0, data,
    hsecond, hnew, _⟩ :=
    nine_ten_normalized_extraction_with_neighbor ctx hb hterminalNot hfirstNot
  exact ⟨cp, hlength, hcomm, hterminal, hfirst, second, actor, E, A0, data,
    hsecond, hnew⟩

end Stellmacher.SectionNine
