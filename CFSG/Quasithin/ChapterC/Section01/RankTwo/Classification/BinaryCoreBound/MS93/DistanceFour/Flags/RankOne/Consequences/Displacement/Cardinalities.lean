module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities.MarkedAction

/-!
# The literal displacement calculation in MS93 (4.6.9)

The noncentral displacement [Z_c,V_alpha] lies in Z_alpha and has order at
most four by the known edge commutator. FlagControl supplies its invariance
modulo the literal central denominator. The marked natural-action theorem
then gives order four and trivial intersection with the intrinsic vertex
center. The same normalization and small-section argument apply to each
outside cyclic layer, whose displacement equals the full displacement.

The commutator homomorphism has kernel V_alpha intersect Q_c, so its image
order is exactly the relative index [V_alpha : V_alpha intersect Q_c].
Finiteness is used only inside actual vertex stabilizers. No critical
endpoint is required; the covering and Bzero deductions remain in
`Consequences.Displacement`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The four literal displacement calculations in the first paragraph of
MS93 (4.6.9), from the flag control and a noncentral edge generator. -/
theorem displacement_cardinalities [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (control : FlagControl source) (c : Vertex R)
    (hac : (cosetGraph R).dist (alpha R) c = 2)
    (hbc : Adjacent R (beta R) c)
    (hnoncentral : ¬ ⁅Z R c, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    Nat.card (⁅Z R c, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
      Disjoint ⁅Z R c, V R (alpha R)⁆
        ((center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) ∧
      (∀ x ∈ Z R c, x ∉ Z R (beta R) →
        Nat.card (⁅zpowers x, V R (alpha R)⁆ : Subgroup (FreeAmalgam R)) = 4) ∧
      (Q R c).relIndex (V R (alpha R)) = 4 := by
  have hlarge : 2 < geometry.b R := by omega
  obtain ⟨i, hkernel, htriple⟩ := control
  have hDZ := displacement_le_Z geometry hlarge early c hac
  have hbound := displacement_card_le_four geometry hlarge early c hbc
  obtain ⟨hnorm, hnormCyclic⟩ := flag_normalizes_full_and_cyclic_displacement
    source geometry hlarge early i hkernel htriple c hbc
  obtain ⟨hcard, hdisjoint⟩ := marked_small_invariant_section source geometry common
    early i hkernel ⁅Z R c, V R (alpha R)⁆ hDZ hbound hnoncentral hnorm
  refine ⟨hcard, hdisjoint, ?_,
    (displacement_index_eq_card source geometry common early c hac hbc).trans hcard⟩
  intro x hx hxout
  have hcyclic := (cyclic_displacement_and_kernel_index source geometry common early
    c hac hbc x hx hxout).1
  exact (marked_small_invariant_section source geometry common early i hkernel
    ⁅zpowers x, V R (alpha R)⁆ (by rwa [hcyclic]) (by rwa [hcyclic])
    (by rwa [hcyclic]) (hnormCyclic x hx)).1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
