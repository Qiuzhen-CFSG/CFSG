module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanOffender
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanOffender

/-!
# The literal terminal intersection of the full local kernels

An actual midpoint-stabilizer conjugator taking a to z places Z_z intersect
B_e inside Z_a join Z_e. Indeed the residual fixes B_e modulo Z_e, while
Q_e normalizes Z_a. Their generation of G_e preserves the seed intersection
joined with Z_e.

Consequently Q_a intersect Q_e fixes the terminal B-intersection. The
literal terminal index budget identifies its moving part with U_z intersect
Q_a. The original full-cover fixed-kernel theorem then places the entire
Q_a intersect Q_e in Z_a join Q_z.

This proves the kernel-placement step in MS93 (3.10)(i), printed p.880.
The internal import reuses its original terminal intersection equality and
vertex generation; no private declaration occurs in the public statement.
No identification [Q_a,L_a]=[W,L_a] or first seed budget is required.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem midpoint_orbit_B_intersection_le_seed_join
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z) :
    Z d.radical z ⊓ B d.radical (path.walk.getVert 2) (geometry.Z_normal _) ≤
      Z d.radical a ⊔ Z d.radical (path.walk.getVert 2) := by
  let e := path.walk.getVert 2
  let B₀ := B d.radical e (geometry.Z_normal e)
  let A := Z d.radical a ⊓ B₀
  let J := A ⊔ Z d.radical e
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hdist : (cosetGraph d.radical).dist e a=2 := by
    rw [SimpleGraph.dist_comm,path.dist_start (by omega)]
  have hVS : V d.radical e ≤ stabilizer d.radical e :=
    (geometry.V_le_Q (by omega) e he).trans (fun _ hx => hx.1)
  have hSB : stabilizer d.radical e ≤ normalizer (B₀ : Set (FreeAmalgam d.radical)) :=
    Escape.Propagation.Rigidity.B_normalized (by omega) e he
  have hAL : ⁅A,Ltilde d.radical e⁆ ≤ Z d.radical e := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff d.radical e (geometry.Z_normal e) hVS x).mp hx.2).2 l hl
  have hLJ : Ltilde d.radical e ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    normalizes_sup_of_displacement _ _ _
      ((Ltilde_le_stabilizer e).trans (Z_normalized d.radical e)) hAL
  have hQS : Q d.radical e ≤ stabilizer d.radical e := fun _ hx => hx.1
  have hQA : Q d.radical e ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    (le_inf ((Q_le_stabilizer_of_dist_two d.radical e a he hdist).trans
      (Z_normalized d.radical a)) (hQS.trans hSB)).trans inf_normalizer_le_normalizer_inf
  have hQJ : Q d.radical e ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    (le_inf hQA (hQS.trans (Z_normalized d.radical e))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hSJ : stabilizer d.radical e ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←inner_stabilizer_eq h d geometry (by omega) he]
    exact sup_le hLJ hQJ
  have hmapB := mem_normalizer_iff_map_conj_eq.mp
    (hSB ((stabilizer d.radical e).inv_mem hg))
  have hmapJ := mem_normalizer_iff_map_conj_eq.mp
    (hSJ ((stabilizer d.radical e).inv_mem hg))
  change B₀.map (MulAut.conj g⁻¹).toMonoidHom = B₀ at hmapB
  change J.map (MulAut.conj g⁻¹).toMonoidHom = J at hmapJ
  have hmapA : A.map (MulAut.conj g⁻¹).toMonoidHom=Z d.radical z ⊓ B₀ := by
    rw [show A=Z d.radical a ⊓ B₀ from rfl,
      Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective,←Z_act,hga,hmapB]
  have hle := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (show A ≤ J from le_sup_left)
  rw [hmapA,hmapJ] at hle
  exact hle.trans (sup_le_sup inf_le_left le_rfl)

/-- The original midpoint orbit and terminal B-index budget place the
whole intersection Q_a intersect Q_e in the original critical root joined
with the full endpoint kernel. The initial seed budget is unnecessary. -/
theorem Input.replacement_distance_four_kernel_intersection_le_root_sup_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    Q d.radical a ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical a ⊔ Q d.radical z := by
  let e := path.walk.getVert 2
  let C₀ := Q d.radical a ⊓ Q d.radical e
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hez : (cosetGraph d.radical).dist e z=2 := by
    rw [path.dist_end,path.length_eq_b,hb]
  have hCS : C₀ ≤ stabilizer d.radical z := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical e z he hez)
  have hCa : C₀ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_left.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a path.start_color)))
  have hCe : C₀ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical e he)))
  have hCjoin : C₀ ≤ centralizer ((Z d.radical a ⊔ Z d.radical e :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hCa) (le_centralizer_iff.mp hCe))
  have hCU : ⁅C₀,U d.radical z ⊓ Q d.radical a⁆=⊥ := by
    rw [terminal_moving_kernel_eq_B h d path hb hlast]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hCjoin.trans (centralizer_le
      ((inf_le_inf_right _ (U_le_Z z)).trans
        (midpoint_orbit_B_intersection_le_seed_join h d path hb g hg hga))))
  have hcrit := h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path
  have hsmall : (Q d.radical z).relIndex (Z d.radical a)<Nat.card F^2 := by
    rw [hcrit.1]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hfull := (h.replacement_root_intersection_fixed_and_commutator d path (by omega)
    hsmall C₀ hCS).1
  rw [h.replacement_distance_four_X_eq_Z d geometry hb path.end_color,hCU] at hfull
  have hfix : C₀ ≤ centralizer ((Z d.radical z ⊓ Q d.radical a :
      Subgroup (FreeAmalgam d.radical)) : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp hfull
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hh := h.replacement_root_Z_intersection_centralizer d path (by omega) hsmall
    (stabilizer d.radical z) hAZ le_rfl
  exact ((le_inf hCS hfix).trans_eq hh).trans (sup_le_sup le_rfl inf_le_right)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
