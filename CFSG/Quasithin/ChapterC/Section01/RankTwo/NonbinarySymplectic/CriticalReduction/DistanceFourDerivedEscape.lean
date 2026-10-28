module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanDerived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalKernelSaturation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanDecomposition

/-!
# A large critical commutator escapes every moved derived subgroup

The actual reciprocal span recognition gives the field-size derived bound
at its selected vertex. Conjugacy of the literal moved radii transports
this bound to every vertex of the same color. The large backward critical
commutator has order strictly greater than the field order, retaining its
entire central kernel, and therefore cannot lie in any such derived group.

This supplies the numerical obstruction used in MS93 (5.12)(2), printed
p.926. It does not assume that the backward endpoint lies in the forward
midpoint orbit, or identify the reciprocal quotient carriers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem moved_derived_card_eq
    {M : Type*} [Group M] {R : Subgroup M} {a v : Vertex R}
    (ha : color R a=false) (hv : color R v=false) :
    Nat.card (⁅Vcirc R a,Vcirc R a⁆ : Subgroup (FreeAmalgam R)) =
      Nat.card (⁅Vcirc R v,Vcirc R v⁆ : Subgroup (FreeAmalgam R)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R hv
  have he : act R (g⁻¹*j) a=v := by
    rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
  rw [←he,Vcirc_act,←map_commutator,
    card_map_of_injective (MulAut.conj (g⁻¹*j)⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual fixed-radius, large-back branch forces the full critical
commutator outside the derived subgroup of every original moved radius. -/
theorem Input.replacement_distance_four_critical_commutator_escapes_moving_derived
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (∀ v : Vertex d.radical, color d.radical v=false →
      Nat.card (⁅Vcirc d.radical v,Vcirc d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) ≤
        Nat.card F) ∧
    ∀ v : Vertex d.radical, color d.radical v=false →
      ¬ ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Vcirc d.radical v,Vcirc d.radical v⁆ := by
  have hbound : ∀ v : Vertex d.radical, color d.radical v=false →
      Nat.card (⁅Vcirc d.radical v,Vcirc d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) ≤
        Nat.card F := by
    rcases h.replacement_distance_four_span_derived_bound_or_reciprocal d path hb
      back hmid hlarge hfixed with ⟨_,hc⟩ | ⟨_,hc⟩
    · intro v hv
      rw [←moved_derived_card_eq path.start_color hv]
      exact hc
    · intro v hv
      rw [←moved_derived_card_eq back.end_color hv]
      exact hc
  have hcard : Nat.card F < Nat.card
      (⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ : Subgroup (FreeAmalgam d.radical)) := by
    rw [h.replacement_critical_commutator_card d back (by omega)]
    let := finite_Z d.radical u
    let C := U d.radical u ⊓
      centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))
    let : Finite C := Finite.of_injective
      (inclusion (inf_le_left.trans (DistanceEight.U_le_Z d.radical u))) (inclusion_injective _)
    exact hlarge.trans_le (Nat.le_mul_of_pos_right _ (Nat.card_pos (α := C)))
  refine ⟨hbound,?_⟩
  intro v hv hle
  let := finite_stabilizer d.radical v
  have hDS : ⁅Vcirc d.radical v,Vcirc d.radical v⁆ ≤ stabilizer d.radical v :=
    (commutator_le_self _).trans ((DistanceEight.Vcirc_le_V d.radical v).trans
      (geometry.V_local v hv (by
        rw [geometry.distance_constant v hv]
        exact (show 2 < geometry.b d.radical by omega))))
  let : Finite (⁅Vcirc d.radical v,Vcirc d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hDS) (inclusion_injective _)
  exact (not_le_of_gt hcard)
    ((Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans (hbound v hv))

/-- A compatible backward path in the prescribed midpoint orbit has both
critical indices exactly the original field order in the fixed-radius
branch. Its orbit witness is literal and is not inferred from distance. -/
theorem Input.replacement_distance_four_fixed_orbit_backward_indices
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) ≤ Nat.card F := by
    by_contra! hlarge
    have hlarge₂ : Nat.card F^2 ≤
        (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u) := by
      by_contra! hlt
      have he := (h.replacement_small_critical_indices_eq_field d back (by omega) hlt).1
      exact (ne_of_gt hlarge) he
    have hn := (h.replacement_distance_four_critical_commutator_escapes_moving_derived
      d path hb back hmid hlarge hfixed).2 a path.start_color
    apply hn
    rw [←h.replacement_distance_four_span_derived_eq_moving_derived d path hb back hlarge₂ hfixed]
    apply commutator_mono _ (Z_le_localZSpan d.radical (path.walk.getVert 2) a)
    rw [←hru]
    exact le_iSup (fun g : stabilizer d.radical a => Z d.radical (act d.radical g
      (path.walk.getVert 2))) ⟨r,hr⟩
  exact h.replacement_small_critical_indices_eq_field d back (by omega) (hsmall.trans_lt (by
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
