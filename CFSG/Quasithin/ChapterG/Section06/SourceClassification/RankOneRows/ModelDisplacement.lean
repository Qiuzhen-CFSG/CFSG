module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleActors.ScalarDegree
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions.Displacement

/-!
# A marked rank-one action forces the binary defining field

The action intertwiner preserves the displacement of the original element.
Its nontrivial faithful action therefore forces the defining-field degree to
be one. This applies to the actual quotient images of B.5.6 factors and the
quasisimple moved section in G.6.4, retaining their original actors.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource

theorem model_field_degree_one_of_rank_one (F : BinaryField)
    {D E V W : Type*} [Group D] [Group E]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] [FiniteDimensional F.Carrier W]
    {ρ : Representation (ZMod 2) D V} (hf : Function.Injective ρ)
    (t : D) (ht : t ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1)
    (σ : Representation F.Carrier E W)
    (e : ActionEquiv ρ (restrictScalars (k := ZMod 2) σ)) : F.degree = 1 := by
  let : FiniteDimensional (ZMod 2) W := Module.Finite.equiv e.linearEquiv
  have hne : σ (e.groupEquiv t) ≠ 1 := by
    intro he
    apply ht
    apply hf
    ext v
    apply e.linearEquiv.injective
    have hh := e.intertwines t v
    change e.linearEquiv (ρ t v) = σ (e.groupEquiv t) (e.linearEquiv v) at hh
    simpa only [he, Module.End.one_apply, map_one] using hh
  have hb := scalar_degree_le_displacement F σ (e.groupEquiv t) hne
  rw [← e.displacement_rank t] at hb
  have hp := F.degree_pos
  omega
end CFSG.Quasithin.ChapterG.Section06
