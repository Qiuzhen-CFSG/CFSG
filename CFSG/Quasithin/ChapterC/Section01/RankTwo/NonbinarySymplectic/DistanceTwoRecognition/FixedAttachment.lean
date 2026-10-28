module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.SharpImages

/-!
# Fixed attachments in the common edge center

Positive critical distance gives inner action of the full edge kernel.
Thus the component-fixed part of X centralizes the edge kernel and lies
in its omega center. In the non-Frattini branch the whole X-decomposition
then gives X = Z and Z = U Z_t, retaining every fixed attachment in Z_t.
These are the literal layer identities used in the remaining secondary
seed-displacement calculation of MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The entire component-fixed part of X is contained in each incident edge
center. Positive distance supplies the full inner edge action. -/
theorem replacement_fixed_X_le_edge
    {g : Geometry d.radical} {a t : Vertex d.radical}
    (hb : 0 < g.b d.radical) (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) ≤
      Z d.radical t := by
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all
  have hcentral : Q d.radical t ≤ centralizer
      ((X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    apply (replacement_inner_edge h d hb ha hat).trans
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      ((Q_le_centralizer_X d.radical a).trans (centralizer_le inf_le_left))
  intro x hx
  simp only [Z,ht,Bool.true_eq_false,↓reduceIte,edgeOmega]
  exact mem_omegaCenter_iff.mpr
    ⟨Q_le_adjacent_h d.radical ht hat ((omegaCenter_le _) hx.1),
      (mem_omegaCenter_iff.mp hx.1).2.1, (le_centralizer_iff.mp hcentral) hx⟩

/-- In the non-Frattini branch, the full central omega layer equals Z.
Its fixed attachment is included via the common edge, not discarded. -/
theorem replacement_nonfrattini_X_eq_Z
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    X d.radical a = Z d.radical a := by
  apply le_antisymm
  · rw [replacement_nonfrattini_X_decomposition h d path hb hlarge]
    exact sup_le (U_le_Z a) ((replacement_fixed_X_le_edge h d (g := g)
      (by omega) path.start_color hat).trans (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat))
  · exact g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]
      change 0 < g.b d.radical
      omega)

/-- The whole Z-layer is U times the common edge center. This preserves the
full fixed layer while reducing the remaining displacement to the cover. -/
theorem replacement_nonfrattini_Z_eq_moving_sup_edge
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    Z d.radical a = U d.radical a ⊔ Z d.radical t := by
  apply le_antisymm
  · rw [←replacement_nonfrattini_X_eq_Z h d path hb hat hlarge,
      replacement_nonfrattini_X_decomposition h d path hb hlarge]
    exact sup_le_sup_left (replacement_fixed_X_le_edge h d (g := g)
      (by omega) path.start_color hat) _
  · exact sup_le (U_le_Z a) (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
