module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# The source domain for the rank-one branches of Chapter K

These hypotheses are exactly the standing hypotheses on printed p.451. The
known-simple catalogue is the full catalogue, and irreducibility is on the
literal restriction to the quasisimple generalized Fitting subgroup. Normality
and triviality of the layer's two-core are deductions: the former comes from
F*, and the latter from the normal p-subgroup fixed-vector theorem.

No module recognition, covering identification or ratio conclusion is encoded
as an input. Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Chapter K, printed pp.451–454.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Chapter K's common domain, before a central-quotient family is selected. -/
structure SourceHypotheses (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  fitting : generalizedFitting G = L
  quasisimple : IsQuasisimple L
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp L.subtype)
  smallCubic : cubicRatio ρ ≤ 2

namespace SourceHypotheses
variable {ρ : Representation (ZMod 2) G V} {L : Subgroup G} (h : SourceHypotheses ρ L)

include h

omit [FiniteDimensional (ZMod 2) V] in
/-- Relative normality in the actual actor follows from the F* identity. -/
theorem layer_normal : L.Normal := h.fitting ▸ inferInstance

/-- A faithful irreducible binary layer has trivial two-core. -/
theorem layer_twoCore_eq_bot : pCore 2 L = ⊥ := by
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hk := normal_p_subgroup_le_ker (ρ.comp L.subtype) (pCore 2 L) pCore_isPGroup
  have hz : (ρ.comp L.subtype).ker = ⊥ :=
    (ρ.comp L.subtype).ker_eq_bot_iff.mpr (h.faithful.comp L.subtype_injective)
  exact bot_unique (hz ▸ hk)

end SourceHypotheses
end CFSG.Quasithin.ChapterK.RankOne
