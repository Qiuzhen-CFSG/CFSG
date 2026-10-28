module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.FiveChiefFactors

/-!
# The original point commutator from the earlier plane noncentrality

The section-centralizer identity makes Q_H act trivially on U/V₁, so its
commutators with U lie in V₁. The actual V₂ lies in U. Thus the earlier
13.3.14 assertion that Q₁ does not centralize V₂ makes this commutator
nontrivial. Here H is the original G₁, so Q₁=Q_H. Since V₁ has order two,
the commutator is exactly V₁.

The chief-factor application now uses that literal earlier noncentrality
assertion, the original marking, and the structural and uniqueness inputs.
It constructs both the required commutator identity and the source duality.
No other part of the full 14.5.21 family is needed for this L₃(2) application.
The universal source 13.3.14 still has to be supplied by its own producer;
the present implication does not prove noncentrality.

Source: Aschbacher–Smith, 13.3.14, printed p.891; 14.5.21(2), printed p.1019;
application to the original L₁ chief-factor calculation in 14.7.70, p.1074.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem core_commutator_le_point (hc : d.SectionCentralizer) :
    ⁅F.H.pCoreIn 2, F.U⁆ ≤ F.Vi 1 := by
  apply commutator_le.mpr
  intro q hq u hu
  let h : F.H := ⟨q, pCoreIn_le 2 F.H hq⟩
  let a : F.U := ⟨u, hu⟩
  have hh : d.action h = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hc]
    exact hq
  let b : F.U := ⟨h * a * (h : G)⁻¹,
    (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) a).mp a.property⟩
  have he : d.conjugationSection.coordinates b = d.conjugationSection.coordinates a := by
    apply Multiplicative.toAdd.injective
    rw [d.conjugationSection.equivariant, hh]
    rfl
  exact (d.conjugationSection.coordinates_eq_one_iff (b * a⁻¹)).mp (by
    rw [map_mul, map_inv, he, mul_inv_cancel])

/-- The earlier Q₁ action on the original plane gives the exact point commutator. -/
theorem Data.U_core_commutator_eq_point_of_plane_moved
    (hc : d.SectionCentralizer)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G)) :
    ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hV : F.Vi 2 ≤ F.U := (F.le_seed 2).trans (le_conjugateSpanBy V F.H)
  have hle := core_commutator_le_point d hc
  have hne : ⁅F.H.pCoreIn 2, F.U⁆ ≠ ⊥ := by
    intro he
    exact hmove ((commutator_eq_bot_iff_le_centralizer.mp he).trans (centralizer_le hV))
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let A := ⁅F.H.pCoreIn 2, F.U⁆
  let : Fact (Nat.card (F.Vi 1)).Prime := ⟨hcard.symm ▸ Nat.prime_two⟩
  have htop : A.subgroupOf (F.Vi 1) = ⊤ := by
    apply (A.subgroupOf (F.Vi 1)).eq_bot_or_eq_top_of_prime_card.resolve_left
    intro he
    apply hne
    have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) he
    rw [map_subgroupOf_eq_of_le (show A ≤ F.Vi 1 from hle), Subgroup.map_bot] at hm
    exact hm
  have hm := congrArg (fun S : Subgroup (F.Vi 1) => S.map (F.Vi 1).subtype) htop
  rw [map_subgroupOf_eq_of_le hle, ← MonoidHom.range_eq_map, range_subtype] at hm
  rw [commutator_comm]
  exact hm

namespace Rechoice.Goldschmidt.LeftChiefFactors

/-- Apply the genuine earlier noncentrality input directly to the original L₁. -/
theorem originalChief_count_of_plane_moved (c : CriticalPath (L := L) F)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (mark : LocalGeometry.Preparation.UpperMarking d)
    (hmove : ¬ F.H.pCoreIn 2 ≤ centralizer (F.Vi 2 : Set G))
    (t : NoncentralChiefRefinement.ChiefSeries (F.Li L 1))
    (ht0 : t.head = ⊥) (ht1 : t.last = ⊤) : 5 ≤ t.noncentralTwoCount :=
  originalChief_count_of_source d c structural uniqueness mark
    (d.U_core_commutator_eq_point_of_plane_moved
      (d.sectionCentralizer_of_earlier_setup structural uniqueness) hmove) t ht0 ht1

end Rechoice.Goldschmidt.LeftChiefFactors

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
