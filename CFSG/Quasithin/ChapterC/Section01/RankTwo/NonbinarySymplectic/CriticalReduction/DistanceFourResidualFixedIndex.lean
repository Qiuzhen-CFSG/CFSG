module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourResidualKernelPlacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanResidual
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The full residual has field-sized terminal movement modulo the original U

The actual midpoint orbit and terminal seed budget place Q_a intersect Q_e
inside Z_a join Q_z. Its commutator with the full Z_z therefore lies in the
original critical commutator, hence in U_a. The initial seed budget bounds
the image of Q0=[Q_a,L_a] modulo Q_e by q. Combining these two literal full
kernel facts bounds the fixed-preimage index for Z_z on Q0 modulo U_a.

This is the next inference of MS93 (3.10)(i), printed p.880. The fixed
preimage is an ambient subgroup, so no abelian or natural quotient of Q0
is assumed, and Q0 is not identified with the native span commutator.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The whole residual intersection has terminal displacement in U_a, and
both actual seed budgets give its full fixed-preimage index at most q. -/
theorem Input.replacement_distance_four_residual_terminal_fixed_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical (path.walk.getVert 2))
    (hga : act d.radical g a=z)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfirst : (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F)
    (hlast : (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z) ≤ Nat.card F) :
    let Q₀ := ⁅Q d.radical a,Ltilde d.radical a⁆
    ⁅Q₀ ⊓ Q d.radical (path.walk.getVert 2),Z d.radical z⁆ ≤ U d.radical a ∧
      (commutatorPreimage Q₀ (Z d.radical z) (U d.radical a)).relIndex Q₀ ≤ Nat.card F := by
  dsimp only
  let Q₀ := ⁅Q d.radical a,Ltilde d.radical a⁆
  let C := ⁅Z d.radical a,Z d.radical z⁆
  have hQ₀ : Q₀ ≤ Q d.radical a := le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (Q_normalized d.radical a))
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega)
  have haS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hCa : C ≤ Z d.radical a := critical_commutator_le_start_seed path
  have hCz : C ≤ Z d.radical z := by
    change ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical z
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp (haS.trans (Z_normalized d.radical z))
  let : IsElementaryAbelian 2 (Z d.radical a) := geometry.Z_elementary (by omega) a path.start_color
  have haC : Z d.radical a ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (Z d.radical a).le_centralizer.trans (centralizer_le hCa)
  have hqC : Q d.radical z ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z path.end_color))).trans (centralizer_le hCz)
  have hjoinC : Z d.radical a ⊔ Q d.radical z ≤ normalizer (C : Set (FreeAmalgam d.radical)) :=
    (sup_le haC hqC).trans (_root_.centralizer_le_normalizer C)
  have hcomm : ⁅Z d.radical a ⊔ Q d.radical z,Z d.radical z⁆ ≤ C := by
    apply commutator_sup_le_of_relative_normal (Z d.radical a ⊔ Q d.radical z)
      (Z d.radical a) (Q d.radical z) (Z d.radical z) C hjoinC le_sup_left le_sup_right le_rfl
    rw [commutator_comm,geometry.centralizes z path.end_color]
    exact bot_le
  have hCU : C ≤ U d.radical a := by
    change ⁅Z d.radical a,Z d.radical z⁆ ≤ U d.radical a
    rw [h.replacement_Z_commutator_eq_U d geometry (by omega) path.start_color _ hzS]
    exact le_normalizer_iff_commutator_le_left.mp (hzS.trans (U_normalized a))
  have hplace := h.replacement_distance_four_kernel_intersection_le_root_sup_kernel d
    path hb g hg hga hfixed hlast
  have hCQ : ⁅Q₀ ⊓ Q d.radical (path.walk.getVert 2),Z d.radical z⁆ ≤ U d.radical a :=
    ((commutator_mono ((inf_le_inf_right _ hQ₀).trans hplace) le_rfl).trans hcomm).trans hCU
  refine ⟨hCQ,?_⟩
  have hpre : Q₀ ⊓ Q d.radical (path.walk.getVert 2) ≤
      commutatorPreimage Q₀ (Z d.radical z) (U d.radical a) :=
    le_commutatorPreimage inf_le_left hCQ
  let := finite_stabilizer d.radical a
  let : Finite Q₀ := Finite.of_injective
    (inclusion (hQ₀.trans (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1)))
    (inclusion_injective _)
  have hi := relIndex_le_of_le_left hpre (L := Q₀) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hi
  exact hi.trans (h.replacement_distance_four_residual_image d path hb hfixed hfirst)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
