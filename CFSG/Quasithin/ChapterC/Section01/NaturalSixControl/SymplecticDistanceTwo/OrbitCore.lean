module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitCommutator
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.CriticalPlane

/-!
# The critical orbit contains the whole symplectic commutator core

The maximal critical plane is the actual intersection Zc intersect Qalpha.
Consequently [Qalpha,Zc] lies in that plane and hence in its normal orbit.
The opposite Z-layer escapes Qalpha, so the native A6/S6 normal-generation
argument puts the entire commutator core in the orbit. Idempotence under the
two-residual then identifies [A,Ltildealpha] with that core. In particular the
contrary large-core branch has nontrivial movement on the literal A/Zalpha.

This is the first noncentrality step of MS93 (3.6), printed p.871, proved
using the binary four-space intersection calculation rather than an additional
orbit-size hypothesis. All maps and critical geometry are the native ones.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

private theorem core_le_criticalOrbit_of_plane_eq (hb : s.geometry.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hplane : criticalPlane R c b = Z R c ⊓ Q R (alpha R)) :
    core R (alpha R) ≤ criticalOrbit R c b := by
  let A := criticalOrbitNative R c b
  let : A.Normal := normalClosure_normal
  let E := (Z R c).comap (embedM R)
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl (by change 0 < s.geometry.b R; omega) c hc0 hc
  have hZ : Z R c ≤ (embedM R).range := by
    rw [← show stabilizer R (alpha R) = (embedM R).range from stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_two R s.geometry c hc0
    · rw [s.geometry.distance_constant c hc0]
      change 0 < s.geometry.b R
      omega
    · rw [SimpleGraph.dist_comm]
      exact hc.1.trans hb
  have hEm : E.map (embedM R) = Z R c :=
    (map_comap_eq _ _).trans (inf_eq_right.mpr hZ)
  have hE : ¬ E ≤ pCore 2 M := by
    intro hh
    apply hrev.2
    rw [←hEm,Q_alpha R s.two_group s.core_le]
    exact map_mono hh
  have hcomm : ⁅Q R (alpha R),Z R c⁆ ≤ criticalPlane R c b := by
    rw [hplane]
    exact le_inf (DistanceTwo.NaturalCore.local_commutator_le_endpoint hab hcb)
      (DistanceTwo.NaturalCore.local_commutator_le_Q s.geometry hb hc)
  have hcomm0 : ⁅pCore 2 M,E⁆ ≤ A := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator,hEm,←Q_alpha R s.two_group s.core_le]
    exact hcomm.trans (s.criticalPlane_le_orbit hb hc b)
  have hcore := map_mono (f := embedM R) (s.core_le_of_commutator_le A E hE hcomm0)
  rwa [←core_alpha R s.two_group s.core_le s.residual] at hcore

private theorem criticalOrbit_commutator_eq_core_of_plane_eq (hb : s.geometry.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    (hne : core R (alpha R) ≠ U R (alpha R))
    (hplane : criticalPlane R c b = Z R c ⊓ Q R (alpha R)) :
    ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ = core R (alpha R) := by
  apply le_antisymm
  · exact commutator_mono ((s.criticalOrbit_le_Q_iff hb hc b).mpr
      (s.criticalPlane_le_Q_of_core_ne hb hc hab hcb hne)) le_rfl
  · rw [←s.core_full_commutation (alpha R) rfl]
    exact commutator_mono (s.core_le_criticalOrbit_of_plane_eq hb hc hab hcb hplane) le_rfl

/-- The critical plane normally generates a subgroup containing the entire
original commutator core. -/
theorem core_le_criticalOrbit (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    core R (alpha R) ≤ criticalOrbit R c b :=
  s.core_le_criticalOrbit_of_plane_eq hb hc hab hcb
    (s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hc hab hcb)

/-- The orbit's moving subgroup is exactly the full commutator core. -/
theorem criticalOrbit_commutator_eq_core (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ = core R (alpha R) := by
  have hne : core R (alpha R) ≠ U R (alpha R) := by
    intro he
    apply hlarge
    rw [he]
    exact ((U_le_Z _).trans s.Z_le_X).trans le_sup_right
  exact s.criticalOrbit_commutator_eq_core_of_plane_eq hb hc hab hcb hne
    (s.criticalPlane_eq_opposite_inf_Q h t hfull hb hlarge hc hab hcb)

/-- The contrary branch has genuine noncentral movement on A/Zalpha. -/
theorem criticalOrbit_commutator_not_le_Z (h : NativeCentralLayer s) (t : S)
    (hfull : R.map s.projection = pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 2)
    (hlarge : ¬ core R (alpha R) ≤
      (frattini (Q R (alpha R))).map (Q R (alpha R)).subtype ⊔ X R (alpha R))
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (s.geometry.exists_critical (alpha R) rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    ¬ ⁅criticalOrbit R c b,Ltilde R (alpha R)⁆ ≤ Z R (alpha R) := by
  rw [s.criticalOrbit_commutator_eq_core h t hfull hb hlarge hc hab hcb]
  exact fun hle => hlarge ((hle.trans s.Z_le_X).trans le_sup_right)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
