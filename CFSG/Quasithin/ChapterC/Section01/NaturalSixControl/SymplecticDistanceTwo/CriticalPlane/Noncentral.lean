module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane.Cardinality

/-!
# The actual critical orbit is moved by the original kernel

The critical plane is strictly larger than the common edge layer. If the
original kernel centralized the plane, the elementary plane would lie in its
omega center. The previously proved intersection of that omega center with
the opposite Z-layer is exactly the edge layer, a contradiction. Inclusion
of the plane in its original conjugate span gives the orbit consequence.
The final theorem applies this to the literal characteristic replacement.

Source: MS93 (3.6), printed p.871.
-/

public section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M] {L R W : Subgroup M} [L.Normal] [W.Normal]
  (s : Source L R W)
include s

/-- The critical plane is moved by the original kernel. -/
theorem criticalPlane_commutator_ne_bot
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅Q R (alpha R),criticalPlane R c b⁆ ≠ ⊥ := by
  intro hzero
  have hstrict := s.criticalPlane_edge_strict h t hfull hb hlarge hc hab hcb
  apply (not_le_of_gt hstrict)
  rw [←s.critical_Z_inf_X_eq_edge h t hfull hb hlarge hc hab hcb]
  apply le_inf (criticalPlane_le_opposite c b)
  have hQ : criticalPlane R c b ≤ Q R (alpha R) := by
    rw [s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hc hab hcb]
    exact inf_le_right
  have hC : criticalPlane R c b ≤ centralizer (Q R (alpha R) : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
  let := s.criticalPlane_elementary hb hc b
  intro y hy
  exact mem_omegaCenter_iff.mpr ⟨hQ hy,
    elemPow_eq_one_of_isElementaryAbelian y hy,hC hy⟩

/-- The literal critical orbit has nonzero commutator with the original kernel. -/
theorem criticalOrbit_commutator_ne_bot
    (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅Q R (alpha R),criticalOrbit R c b⁆ ≠ ⊥ := by
  intro hzero
  apply s.criticalPlane_commutator_ne_bot h t hfull hb hlarge hc hab hcb
  apply le_bot_iff.mp
  exact (commutator_mono le_rfl (s.criticalPlane_le_orbit hb hc b)).trans_eq hzero

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T)

/-- The actual characteristic replacement has a critical orbit with nonzero
commutator under the original kernel. -/
theorem reducedSource_criticalOrbit_commutator_ne_bot (h : IntrinsicMSPair d)
    (r : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hfull : r.radical.map ((originalSource d h).reduce r).projection =
      pointCore.map (MulAut.conj d.relabeler.val⁻¹).toMonoidHom)
    (hb : ((originalSource d h).reduce r).geometry.b r.radical = 2)
    (hlarge : ¬ core r.radical (alpha r.radical) ≤
      (frattini (Q r.radical (alpha r.radical))).map
        (Q r.radical (alpha r.radical)).subtype ⊔ X r.radical (alpha r.radical))
    {c b : Vertex r.radical}
    (hc : CriticalPair r.radical (alpha r.radical) c
      (((originalSource d h).reduce r).geometry.exists_critical (alpha r.radical) rfl))
    (hab : Adjacent r.radical (alpha r.radical) b)
    (hcb : Adjacent r.radical c b) :
    ⁅Q r.radical (alpha r.radical),criticalOrbit r.radical c b⁆ ≠ ⊥ :=
  Source.criticalOrbit_commutator_ne_bot ((originalSource d h).reduce r)
    (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ hfull hb hlarge hc hab hcb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
