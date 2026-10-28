module
public import Theory.GroupTheory.CentralizerDisplacementNormalization
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CriticalGeneration

/-!
# The original centralizer kernel in the strict-index argument

The intersection U_d intersect B_a moves under the residual only into Z_a,
which Q_a centralizes. The edge kernel normalizes the intersection itself.
Residual-edge generation therefore proves local normality of the actual
T0=C_Qa(U_d intersect B_a). Its fixed index on U_d is at most the original
B-index. For distance greater than four it contains the whole radius V_a.

A neighboring seed in B_a would likewise make its join with Z_a locally
normal; this supplies genuine moving neighbors in the tensor consumer.
Source: MS93 (5.8)--(5.9), printed pp.919--920. No strict moving index or
critical-distance bound is asserted here.
-/

public section
open Subgroup
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}

/-- Residual displacement into Z and edge normalization prove the full
local normality of the literal source T0. -/
theorem kernelCentralizer_normalized_at_edge
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    {a d t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    stabilizer R a ≤ normalizer (kernelCentralizer geometry a d : Set _) := by
  let A := U R d ⊓ B R a (geometry.Z_normal a)
  have hV : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hAL : ⁅A,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hV x).mp hx.2).2 l hl
  have hL : Ltilde R a ≤ normalizer (kernelCentralizer geometry a d : Set _) :=
    normalizes_inf_centralizer_of_displacement (Ltilde R a) (Q R a) A (Z R a)
      ((Ltilde_le_stabilizer a).trans (Q_normalized R a))
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a ha))) hAL
  have hta : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have htd : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hTA : Q R t ≤ normalizer (A : Set _) :=
    (le_inf (htd.trans (U_normalized d))
      (hta.trans (Escape.Propagation.Rigidity.B_normalized hb a ha))).trans
        inf_normalizer_le_normalizer_inf
  have hT : Q R t ≤ normalizer (kernelCentralizer geometry a d : Set _) :=
    (le_inf (hta.trans (Q_normalized R a))
      (hTA.trans (normalizer_le_normalizer_centralizer A))).trans
        inf_normalizer_le_normalizer_inf
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation R hgen ha hat]
  exact sup_le hL hT

/-- T0 fixes the complete intersection defining the original B-index. -/
theorem kernelCentralizer_moving_index_le
    (geometry : Geometry R) (a d : Vertex R) :
    (centralizer (kernelCentralizer geometry a d : Set _)).relIndex (U R d) ≤
      (B R a (geometry.Z_normal a)).relIndex (U R d) := by
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective (inclusion (U_le_Z d)) (inclusion_injective _)
  have hC : U R d ⊓ B R a (geometry.Z_normal a) ≤
      centralizer (kernelCentralizer geometry a d : Set _) :=
    le_centralizer_iff.mp inf_le_right
  have hi := relIndex_le_of_le_left hC (L := U R d) index_ne_zero_of_finite
  rwa [inf_relIndex_left] at hi

/-- A neighboring seed lying in B would give a locally normalized join. -/
theorem neighbor_join_normalized_of_le_B
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (hgen : pResidual 2 M ⊔ R = ⊤)
    {a d t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hB : Z R d ≤ B R a (geometry.Z_normal a)) :
    stabilizer R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  have hV : V R a ≤ stabilizer R a :=
    (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hAL : ⁅Z R d,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hV x).mp (hB hx)).2 l hl
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation R hgen ha hat]
  exact sup_le (normalizes_sup_of_displacement _ _ _
    ((Ltilde_le_stabilizer a).trans (Z_normalized R a)) hAL)
    (edge_normalizes_neighbor_seed_join hat hdt)

/-- At distance greater than four, the complete original radius belongs
to T0; no quotient or chosen constituent replaces it. -/
theorem radius_le_kernelCentralizer_at_edge
    (geometry : Geometry R) (hb : 4 < geometry.b R)
    {a d t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    V R a ≤ kernelCentralizer geometry a d := by
  have hU : U R d ≤ V R a :=
    (U_le_Z d).trans (le_sup_left.trans (neighbor_seed_join_le_radius hat hdt))
  have hV := le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R ha hb)
  exact le_inf (geometry.V_le_Q (by omega) a ha)
    (hV.trans (centralizer_le (show (U R d ⊓ B R a (geometry.Z_normal a) : Subgroup (FreeAmalgam R)) ≤ V R a from
      inf_le_left.trans hU)))
end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.StrictIndex
