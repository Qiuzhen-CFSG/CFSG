module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic-core inputs for outer four-actor reselection

The expected Sylow extension of odd-prime PSU₃ has a cyclic subgroup of
index four. Outside the socle, every involution either inverts this cyclic
subgroup or belongs to one exceptional pair differing by the marked inner
involution. The separate fusion input moves that exceptional involution,
fixing the marked involution, to an inverter still in the supplied Sylow.

These are conditional interfaces, not assertions of unitary structure or
fusion. Their producers must construct them from the actual source models.
The reselection argument uses the inverter to bound the actor centralizer
by eight, then uses the central four-group to prove commutativity.

Source application: Aschbacher--Smith E.1.14(7), printed p.214, referring
to Aschbacher (1982), Lemma 4.11; the inner Sylow shape is A.3.21(b), p.55.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G : Type*} [Group G]

/-- The cyclic core and the exceptional pair of outer involutions. There is
no conjugacy or centralizer-commutativity conclusion in this interface. -/
structure CyclicCoreData (L T : Subgroup G) (z : G) where
  core : Subgroup G
  cyclic : IsCyclic core
  core_le_inner : core ≤ L
  core_le_sylow : core ≤ T
  core_relIndex : core.relIndex T ≤ 4
  z_mem : z ∈ core
  exceptional : G
  exceptional_mem : exceptional ∈ T
  exceptional_not_inner : exceptional ∉ L
  exceptional_sq : exceptional ^ 2 = 1
  dichotomy : ∀ t ∈ T, t ∉ L → t ^ 2 = 1 →
    t = exceptional ∨ t = z * exceptional ∨
      ∀ x ∈ core, t * x * t⁻¹ = x⁻¹

/-- Fusion of the single exceptional involution, with the marked inner
involution fixed. This does not assume abelianness of either centralizer. -/
@[expose] def ExceptionalFusion {L T : Subgroup G} {z : G}
    (d : CyclicCoreData L T z) : Prop :=
  ∃ g : G, MulAut.conj g z = z ∧ MulAut.conj g d.exceptional ∈ T ∧
    ∀ x ∈ d.core,
      MulAut.conj g d.exceptional * x * (MulAut.conj g d.exceptional)⁻¹ = x⁻¹

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
