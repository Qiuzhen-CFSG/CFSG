module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Layers

/-!
# The remaining local auxiliary calculation on MS93 p.907

The moving part of Y/U and X/Z_alpha require actual natural rank-one
coordinates for the full local actor. The other targets retain the full
first-actor triple and the source decomposition of U. `LocalStructure`
records these intermediate conclusions; it has no constructor here.
Naturality of X does imply the genuine nontriviality of [D,Q] modulo
Z_alpha and D greater than U, as proved below. Constructing those natural
coordinates remains a separate obligation from the p.908 escape argument.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907.
The actor defining D and the actors in the displayed local calculations
are untilded L, hence the full binary parabolics.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- Actual local conclusions of the binary auxiliary calculation, not source
hypotheses. Both module factors include surjective compatible coordinate maps. -/
structure LocalStructure (source : LocalSource L R) (i : Bool) (d : M) where
  moving : RankOnePairing.RankOneFactor (localFlagActor source (!i) d)
    (⁅Y source i d, localFlagActor source (!i) d⁆ ⊔ secondFlagLayer source i d)
    (secondFlagLayer source i d)
  moving_actor_kernel : moving.projection.ker =
    (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d)
  natural : RankOnePairing.RankOneFactor (localFlagActor source (!i) d)
    (X source i d) (Z R (alpha R))
  natural_actor_kernel : natural.projection.ker =
    (localFlagKernel source (!i) d).subgroupOf (localFlagActor source (!i) d)
  first_triple : ∀ g : M, flagIncident source i g d →
    ⁅⁅X source i d, localFlagKernel source i g⁆, localFlagActor source i g⁆ ≤ Z R (alpha R)
  second_commutator : ⁅secondFlagLayer source i d, localFlagActor source (!i) d⁆ ≤ X source i d
  second_decomposition : ∀ g : M, flagIncident source i g d →
    secondFlagLayer source i d =
      commutatorPreimage (firstFlagLayer (R := R) g) (localFlagKernel source (!i) d)
        (Z R (alpha R)) ⊔ X source i d

namespace LocalStructure
variable {source : LocalSource L R} {i : Bool} {d : M}

/-- Actual natural coordinates give the source order four, not just a dimension label. -/
theorem X_index (s : LocalStructure source i d) :
    (Z R (alpha R)).relIndex (X source i d) = 4 := by
  let := s.natural.kernel_normal
  rw [relIndex, index_eq_card, Nat.card_congr s.natural.quotientEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The displacement defining X is nonzero modulo the original Z_alpha. -/
theorem core_commutator_not_le (s : LocalStructure source i d) :
    ¬ ⁅D source i d, localFlagKernel source (!i) d⁆ ≤ Z R (alpha R) := by
  intro h
  have he : (Z R (alpha R)).relIndex (X source i d) = 1 :=
    relIndex_eq_one.mpr (sup_le h le_rfl)
  rw [s.X_index] at he
  contradiction

/-- Naturality of X forces the literal fixed preimage to be strictly larger than U. -/
theorem D_ne_second (s : LocalStructure source i d) (geometry : Geometry R)
    (hlarge : 2 < geometry.b R) : D source i d ≠ secondFlagLayer source i d := by
  intro he
  apply s.core_commutator_not_le
  rw [he]
  exact Incident.secondFlagLayer_commutator_le_Z source geometry hlarge i d

end LocalStructure
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
