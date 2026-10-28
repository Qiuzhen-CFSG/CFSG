module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SelectedCriticalPrefix
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.SelectedBounds

/-!
# The radius-four terminal actor under critical-prefix control

The retained turn places the terminal Z-layer in the opposite local span.
Every generator Z_z of the radius-four actor is at distance at most b-2
from its center. Strictly nearer generators commute with the whole span;
at distance b-2 the endpoint version of critical-prefix control applies.
The fixed core is normalized by the containing kernel, so these generator
bounds extend to the entire radius-four actor.

Source: Meierfrankenfeld--Stellmacher (1993), conclusion of (4.4), p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
open FinalCalculation FinalCalculation.Conclusion FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The literal terminal product lies in the fixed core at index b-2,
using local control only on critical prefixes. -/
theorem terminalProduct_le_fixed (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a) :
    terminalProduct e ≤ fixedCore R (e.walk.getVert (geometry.b R - 2)) := by
  have heven : Even (geometry.b R) := geometry.even (alpha R) rfl
  have hb8 : 8 ≤ geometry.b R := by
    rw [Nat.even_iff] at heven
    omega
  have heven2 : Even (geometry.b R - 2) := by
    rw [Nat.even_iff] at heven ⊢
    omega
  have heven4 : Even (geometry.b R - 4) := by
    rw [Nat.even_iff] at heven ⊢
    omega
  have hc2 := ExtendedPath.vertex_color e heven2 (by omega)
  have hc4 := ExtendedPath.vertex_color e heven4 (by omega)
  have hQ (i : ℕ) (hi : i = geometry.b R - 2 ∨ i = geometry.b R - 4)
      (hc : color R (e.walk.getVert i) = false) :
      VBall R a 4 ≤ Q R (e.walk.getVert i) := by
    apply (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le
      (e.walk.getVert i) a 4 i ?_).trans
      (Escape.Propagation.RadiusFour.VBall_le_Q _ hc _ (by rcases hi with rfl | rfl <;> omega))
    have hd := ExtendedPath.distance e (i := 4) (j := i)
      (by rcases hi with rfl | rfl <;> omega) (by rcases hi with rfl | rfl <;> omega)
    rw [e.center_eq] at hd
    rw [hd]
    rcases hi with rfl | rfl <;> omega
  obtain ⟨g, hg, ht⟩ := e.turns (geometry.b R - 2) heven2 (by omega) (by omega)
  have ht' : act R g (e.walk.getVert (geometry.b R)) =
      e.walk.getVert (geometry.b R - 4) := by
    simpa only [show geometry.b R - 2 + 2 = geometry.b R by omega,
      show geometry.b R - 2 - 2 = geometry.b R - 4 by omega] using ht
  have hinv : act R g⁻¹ (e.walk.getVert (geometry.b R - 4)) =
      e.walk.getVert (geometry.b R) := by
    rw [← ht', ← act_mul, mul_inv_cancel, act_one]
  have hspan : Z R (e.walk.getVert (geometry.b R)) ≤
      localZSpan R (e.walk.getVert (geometry.b R - 4))
        (e.walk.getVert (geometry.b R - 2)) := by
    have hh := le_iSup (fun k : stabilizer R (e.walk.getVert (geometry.b R - 2)) =>
      Z R (act R k (e.walk.getVert (geometry.b R - 4))))
        ⟨g⁻¹, (stabilizer R _).inv_mem hg⟩
    simpa only [localZSpan, hinv] using hh
  let c := e.walk.getVert (geometry.b R - 2)
  let d := e.walk.getVert (geometry.b R - 4)
  let S := localZSpan R d c
  have hdc : (cosetGraph R).dist d c = 2 := by
    dsimp [c, d]
    rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  have hactors : VBall R a 4 ≤ commutatorPreimage (Q R c) S (fixedCore R c) := by
    apply (Escape.Propagation.RadiusFour.Forward.VBall_le_iff (ExtendedPath.center_color e) _).mpr
    intro z hz hza
    have hZa : Z R z ≤ VBall R a 4 := le_iSup_of_le z (le_iSup_of_le hza le_rfl)
    apply le_commutatorPreimage (hZa.trans (hQ _ (Or.inl rfl) hc2))
    rw [commutator_comm]
    have hdist : (cosetGraph R).dist c z + 2 ≤ geometry.b R := by
      have hca := ExtendedPath.distance e (i := 4) (j := geometry.b R - 2)
        (by omega) (by omega)
      rw [e.center_eq] at hca
      have htri := (cosetGraph_connected R).dist_triangle (u := z) (v := a) (w := c)
      dsimp [c] at htri ⊢
      rw [hca, SimpleGraph.dist_comm (u := z) (v := e.walk.getVert (geometry.b R - 2))] at htri
      omega
    by_cases hlt : (cosetGraph R).dist c z + 2 < geometry.b R
    · have hSQ : S ≤ Q R z := (localZSpan_le_V R hdc.le).trans
        (Escape.Initial.Consequences.V_le_Q_of_distance hc2 hlt)
      have hzero : ⁅Q R z, Z R z⁆ = ⊥ := by
        rw [commutator_comm]
        exact geometry.centralizes z hz
      exact ((commutator_mono hSQ le_rfl).trans_eq hzero).trans bot_le
    · exact LocalCommutator.endpoint_commutator_le_fixed_of_criticalPrefix (by omega)
        hprefix hc4 hc2 hdc hz (by omega)
        (le_inf (hZa.trans (hQ _ (Or.inr rfl) hc4))
          (hZa.trans (hQ _ (Or.inl rfl) hc2)))
  rw [terminalProduct, commutator_comm]
  exact (commutator_mono hactors hspan).trans
    (commutator_commutatorPreimage_le _ _ _
      ((show Q R c ≤ stabilizer R c from fun _ hx => hx.1).trans (fixedCore_normalized R c)))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
