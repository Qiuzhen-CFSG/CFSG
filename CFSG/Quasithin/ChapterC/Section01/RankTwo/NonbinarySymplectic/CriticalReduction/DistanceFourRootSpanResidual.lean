module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RadiusFixedCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexSaturation

/-!
# The full residual kernel in the actual root-span branch

Retain Q0=[Q_a,L_a] as a subgroup of the original amalgam. Three-subgroups
makes the full fixed preimage B_a centralize Q0 under the fixed-radius
hypothesis. A literal midpoint seed budget then bounds the image of Q0
modulo the entire Q_e kernel by the original field order.

This is the first full-kernel step of MS93 (3.10)(i), printed p.880.
It does not identify Q0 with [W,L_a] or with the moved radius.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- The full fixed preimage centralizes the residual commutator of the
whole local kernel, using the literal fixed-radius condition. -/
theorem radius_residual_centralizes_full_B
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a=false)
    (hfixed : ⁅V R a,Q R a⁆ ≤ fixedCore R a) :
    ⁅⁅Q R a,Ltilde R a⁆,B R a (geometry.Z_normal a)⁆=⊥ := by
  let D := B R a (geometry.Z_normal a)
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V R a ≤ stabilizer R a := hVQ.trans (fun _ hx => hx.1)
  have hDV : D ≤ V R a := fun x hx =>
    ((mem_B_iff R a (geometry.Z_normal a) hVS x).mp hx).1
  have hDL : ⁅D,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hVS x).mp hx).2 l hl
  have hLDQ : ⁅⁅Ltilde R a,D⁆,Q R a⁆=⊥ := by
    apply le_bot_iff.mp
    rw [commutator_comm (Ltilde R a)]
    exact (commutator_mono hDL le_rfl).trans_eq (Z_centralizes_Q R a ha)
  have hDQL : ⁅⁅D,Q R a⁆,Ltilde R a⁆=⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hDV le_rfl).trans hfixed).trans inf_le_right)
  exact commutator_commutator_eq_bot_of_rotate hLDQ hDQL

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The original midpoint seed budget bounds the full residual kernel
image at that midpoint, without a whole-span naturality hypothesis. -/
theorem Input.replacement_distance_four_residual_image
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hi : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F) :
    (Q d.radical (path.walk.getVert 2)).relIndex
      ⁅Q d.radical a,Ltilde d.radical a⁆ ≤ Nat.card F := by
  let e := path.walk.getVert 2
  let P := ⁅Q d.radical a,Ltilde d.radical a⁆
  let B₀ := B d.radical a (geometry.Z_normal a)
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hPB : P ≤ centralizer (B₀ : Set (FreeAmalgam d.radical)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (radius_residual_centralizes_full_B geometry (by omega) path.start_color hfixed)
  have hUC : U d.radical e ⊓ B₀ ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (le_centralizer_iff.mp hPB)
  let := finite_Z d.radical e
  let : Finite (U d.radical e) :=
    Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  have hidx := relIndex_le_of_le_left hUC (L := U d.radical e) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hidx
  have hPQ : P ≤ Q d.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (Q_normalized d.radical a))
  exact h.replacement_field_fixed_index_image_bound d geometry (by omega) he P
    (hPQ.trans (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd))
    (hidx.trans hi)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
