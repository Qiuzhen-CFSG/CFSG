module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitClassTwo
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.Critical

/-!
# The critical orbit lies inside the original core in the unresolved branch

If the critical plane escapes Q-alpha, its normal closure contains the actual
alternating component. The orbit commutator bound then puts the whole commutator
core in Z-alpha. Idempotence under the two-residual makes that core equal U-alpha.
Consequently the branch core != U has its plane and orbit inside Q-alpha and has
an elementary central quotient, with no additional plane-containment premise.

Source: the native symplectic case of MS93 (3.6), printed p.871. This proves the
containment needed for the orbit section; the natural-section recognition and
the source's noncentrality contradiction remain subsequent steps.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

/-- In the branch still requiring reconstruction, the actual plane lies in
Q-alpha. Otherwise its normal orbit contains L and makes the core equal U. -/
theorem criticalPlane_le_Q_of_core_ne (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    criticalPlane R c t ≤ Q R (alpha R) := by
  by_contra hnY
  let A := criticalOrbitNative R c t
  let : A.Normal := normalClosure_normal
  have hnA : ¬ A ≤ pCore 2 M := by
    intro hA
    apply hnY
    apply (s.criticalPlane_le_orbit hb hc t).trans
    rw [criticalOrbit,Q_alpha R s.two_group s.core_le]
    exact map_mono hA
  have hL := s.residual_le_of_not_le_core A hnA
  have hLg : Ltilde R (alpha R) ≤ criticalOrbit R c t := by
    rw [Ltilde_alpha,s.residual]
    exact map_mono hL
  have hcore : core R (alpha R) ≤ Z R (alpha R) :=
    (commutator_mono le_rfl hLg).trans (s.criticalOrbit_commutator_le hb hc hat hct)
  apply hne
  apply le_antisymm
  · rw [←s.core_full_commutation (alpha R) rfl]
    exact commutator_mono hcore le_rfl
  · exact DistanceTwo.U_le_core s.geometry (by omega) (alpha R) rfl

/-- Literal finite-carrier containment for the remaining module calculation. -/
theorem criticalOrbitNative_le_core_of_core_ne (hb : s.geometry.b R = 2)
    {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    criticalOrbitNative R c t ≤ pCore 2 M := by
  apply (map_le_map_iff_of_injective (embedM_injective R)).mp
  rw [←Q_alpha R s.two_group s.core_le]
  exact (s.criticalOrbit_le_Q_iff hb hc t).mpr
    (s.criticalPlane_le_Q_of_core_ne hb hc hat hct hne)

/-- The source's unresolved branch has an actual elementary central quotient,
without assuming elementary abelianness of its critical orbit. -/
theorem criticalOrbitNative_centerQuotient_elementary_of_core_ne
    (hb : s.geometry.b R = 2) {c t : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hat : Adjacent R (alpha R) t) (hct : Adjacent R c t)
    (hne : core R (alpha R) ≠ U R (alpha R)) :
    IsElementaryAbelian 2 ((criticalOrbitNative R c t) ⧸ center (criticalOrbitNative R c t)) :=
  s.criticalOrbitNative_centerQuotient_elementary hb hc hat hct
    (s.criticalPlane_le_Q_of_core_ne hb hc hat hct hne)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
