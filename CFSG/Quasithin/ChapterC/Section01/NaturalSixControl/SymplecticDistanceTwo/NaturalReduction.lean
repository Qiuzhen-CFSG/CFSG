module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Critical
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayer

/-!
# Native A₆ distance-two reduction

The actual source FF calculation identifies the whole moving Z-layer with its
marked natural module. The Frattini-small case of MS93 (3.6) therefore gives
the whole core immediately. In the other case every genuine critical pair
has the commutator noncontainment needed for the symplectic calculation of
MS93 (3.3)(ii) and (3.6), printed pp.866–871.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- The source's own SQTK premise gives the exact native (3.6) first branch,
or the input to its remaining critical-pair calculation. -/
theorem distance_two_core_or_critical
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hb : s.geometry.b R = 2) :
    core R (alpha R) = W.map (embedM R) ∨
      ∀ c, CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl) →
        ¬ ⁅Q R (alpha R),Z R c⁆ ≤
          ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆ := by
  obtain ⟨hX,hU⟩ := s.natural_moving_layer hsq
  rcases s.core_eq_moving_or_critical_noncontainment hb hX with he | hl
  · exact Or.inl (he.trans hU)
  · exact Or.inr hl

/-- In the small branch the literal intrinsic component core equals the
original marked natural subgroup. -/
theorem intrinsic_core_eq_marked_of_frattini
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hsmall : core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R)) :
    (blockU L).map L.subtype = W := by
  obtain ⟨hX,hU⟩ := s.natural_moving_layer hsq
  have he := s.core_eq_U_of_le_frattini_sup (alpha R) rfl hX hsmall
  have hm := s.original_core_pullback
  rw [he,hU] at hm
  simpa only [comap_map_eq_self_of_injective (embedM_injective R)] using hm.symm

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
