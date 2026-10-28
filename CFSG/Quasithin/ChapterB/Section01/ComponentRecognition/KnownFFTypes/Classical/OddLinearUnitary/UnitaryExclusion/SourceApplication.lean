module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
public import CFSG.Quasithin.ChapterK.Section01To04.OddCharacteristic

/-!
# Discharging K.2's odd unitary restriction

The completed parameter theorem supplies the exact `UnitaryRestriction`
consumed by Chapter K on the original ambient representation. The surviving
central quotient is identified with the actual derived subgroup of G₂(2)
using the existing arbitrary-form PSU₃(3) comparison.

The final theorem applies the completed unitary restriction to K.2's family
assembly. Only the independent odd-linear restriction and Theorem C family
input remain explicit, owned by the odd-linear and Theorem C producers.

Sources: Aschbacher–Smith K.2, printed p.453; Guralnick–Malle,
*Classification of 2F-modules I*, Proposition 4.3, manuscript pp.10–11.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)

/-- The exact odd-unitary premise of the Chapter K assembly, proved without
additional representation or model hypotheses. -/
theorem source_unitaryRestriction : ChapterK.OddCharacteristic.UnitaryRestriction ρ L := by
  intro h p hp ho hm hq
  let : IsQuasisimple L := h.quasisimple
  exact source_parameter_eq_three ρ L
    ⟨h.sqtk, h.generalizedFitting_eq.symm, h.faithful, h.irreducible, hp, ho, hm⟩ hq

/-- The unitary K.2 branch reaches K.3 through an actual isomorphism of the
original central quotient with the derived binary G₂ model. -/
theorem source_g2Derived_of_cubicRatio_le_two
    (h : ChapterK.OddCharacteristic.SourceHypotheses ρ L)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU (L ⧸ center L) 3 p) (hq : cubicRatio ρ ≤ 2) :
    Nonempty ((L ⧸ center L) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  have he := source_unitaryRestriction ρ L h hp ho hm hq
  subst p
  exact ChapterK.OddCharacteristic.g2Derived_of_psu3_three hm

/-- Application to the existing source-family consumer, discharging its
unitary premise. The independent linear restriction and earlier Theorem C
family input retain their original contracts. -/
theorem source_coincidence_of_linearRestriction
    (h : ChapterK.OddCharacteristic.SourceHypotheses ρ L)
    (hl : ChapterK.OddCharacteristic.LinearRestriction ρ L)
    (hf : ChapterK.OddCharacteristic.SourceFamily (L ⧸ center L))
    (hq : cubicRatio ρ ≤ 2) : ChapterK.OddCharacteristic.IsCoincidence (L ⧸ center L) :=
  ChapterK.OddCharacteristic.coincidence_of_cubicRatio_le_two ρ L h hl
    (source_unitaryRestriction ρ L) hf hq

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.UnitaryExclusion
