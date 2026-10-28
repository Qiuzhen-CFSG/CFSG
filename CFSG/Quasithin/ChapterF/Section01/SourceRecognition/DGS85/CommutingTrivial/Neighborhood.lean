module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.Graph
public import Theory.ElementaryAbelian.CommutingFamily

/-!
# Elementary neighboring spans and their quadratic action

The global DGS minimum bounds every center's escape from the full local
kernel. DGS 6.2(d), supplied as an actual Sylow of that kernel whose ambient
image is Q, converts this to core containment. Centers less than b apart
therefore commute. A ball of radius r with 2r < b generates an elementary
abelian subgroup. At distance at most b - 1 the two radius-one spans
normalize one another, so their commutator lies in both and centralizes both.

This supplies the elementary and quadratic assertions used in DGS 9.1(c),
from the earlier core facts and the odd-distance consequence b > 2. The
latter consequence and the local Sylow assertion are separate source inputs.
All normalizers and cores refer to the original action and ambient subgroups.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, 3.8, 6.2(d), 8.1(e), and 9.1(c), printed pp.82--83, 119, 133, 141.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)

/-- The intrinsic core is normalized by its vertex stabilizer. -/
theorem stabilizer_normalizes_Q (v : Vertex F) :
    stabilizer F v ≤ normalizer (Q F v : Set G) := by
  have hn := (pCore 2 (stabilizer F v)).le_normalizer_map (stabilizer F v).subtype
  simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
    range_subtype] using hn

/-- DGS 6.2(d) places every two-subgroup of U in its normal Sylow Q. -/
theorem two_subgroup_le_Q [∀ i, Finite (F i)] (v : Vertex F)
    (hS : ∃ T : Sylow 2 (U F v), (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    {A : Subgroup G} (hA : IsPGroup 2 A) (hAU : A ≤ U F v) : A ≤ Q F v := by
  obtain ⟨T, hT⟩ := hS
  have hQU : Q F v ≤ U F v := hT ▸ map_subtype_le _
  let : ((Q F v).subgroupOf (U F v)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQU).mpr
      ((U_le_stabilizer F v).trans (stabilizer_normalizes_Q F v))
  have hQT : (Q F v).subgroupOf (U F v) = (T : Subgroup (U F v)) := by
    apply map_injective (U F v).subtype_injective
    rw [map_subgroupOf_eq_of_le hQU, hT]
  let : (T : Subgroup (U F v)).Normal := hQT ▸ inferInstance
  let : Finite (U F v) := Finite.of_injective
    (inclusion (U_le_stabilizer F v)) (inclusion_injective _)
  let := Sylow.unique_of_normal T inferInstance
  obtain ⟨R, hR⟩ := (hA.comap_subtype (K := U F v)).exists_le_sylow
  have hRT : R = T := Subsingleton.elim _ _
  rw [hRT] at hR
  have hm := map_mono (f := (U F v).subtype) hR
  change (A.subgroupOf (U F v)).map (U F v).subtype ≤
    (T : Subgroup (U F v)).map (U F v).subtype at hm
  rwa [map_subgroupOf_eq_of_le hAU, hT] at hm

/-- The earlier central-omega containment makes each actual Z elementary abelian. -/
theorem Z_elementary (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v)) (v : Vertex F) :
    IsElementaryAbelian 2 (Z F v) := IsElementaryAbelian.of_le (hZ v)

/-- Short-distance containment is in Q once the full kernel Sylow is supplied. -/
theorem Z_le_Q_of_dist_lt_b [∀ i, Finite (F i)]
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v w : Vertex F) (hd : (graph F).dist v w < b F) : Z F v ≤ Q F w := by
  let := Z_elementary F hZ v
  exact two_subgroup_le_Q F w (hS w) (IsElementaryAbelian.isPGroup 2 _)
    (Z_le_U_of_dist_lt_b F v w hd)

/-- Centers at distance strictly below the global minimum commute. -/
theorem short_centers_commute [∀ i, Finite (F i)]
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v w : Vertex F) (hd : (graph F).dist v w < b F) :
    Z F v ≤ centralizer (Z F w : Set G) := by
  apply le_centralizer_iff.mp
  intro x hx
  exact centralizer_le (Z_le_Q_of_dist_lt_b F hZ hS v w hd)
    ((mem_omegaCenterIn_iff _ _).mp (hZ w hx)).2.1

/-- A ball shorter than b generates a subgroup of the center vertex core. -/
theorem V_le_Q [∀ i, Finite (F i)] (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v : Vertex F) {r : ℕ} (hr : r < b F) : V F v r ≤ Q F v := by
  apply iSup_le
  intro w
  apply iSup_le
  intro hw
  apply Z_le_Q_of_dist_lt_b F hZ hS w v
  rw [SimpleGraph.dist_comm]
  exact ((mem_ball_iff F hgen v w r).mp hw).trans_lt hr

/-- Centers in a ball of diameter less than b generate an elementary abelian group. -/
theorem V_elementary [∀ i, Finite (F i)] (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v : Vertex F) {r : ℕ} (hr : 2 * r < b F) : IsElementaryAbelian 2 (V F v r) := by
  let E : ball F v r → Subgroup G := fun w => Z F w.val
  let : ∀ w, IsElementaryAbelian 2 (E w) := fun w => Z_elementary F hZ w.val
  have hc : ∀ w z, E w ≤ centralizer (E z : Set G) := by
    intro w z
    apply short_centers_commute F hZ hS w.val z.val
    have hw := (mem_ball_iff F hgen v w.val r).mp w.property
    have hz := (mem_ball_iff F hgen v z.val r).mp z.property
    have ht := (connected F hgen).dist_triangle (u := w.val) (v := v) (w := z.val)
    rw [SimpleGraph.dist_comm (u := w.val) (v := v)] at ht
    omega
  have he : V F v r = ⨆ w, E w := by
    apply le_antisymm
    · apply iSup_le
      intro w
      apply iSup_le
      intro hw
      exact le_iSup E ⟨w, hw⟩
    · apply iSup_le
      intro w
      exact le_iSup_of_le w.val (le_iSup_of_le w.property le_rfl)
  rw [he]
  exact IsElementaryAbelian.iSup_of_le_centralizer E hc

/-- The original vertex stabilizer normalizes the entire closed-ball span. -/
theorem stabilizer_normalizes_V [∀ i, Finite (F i)] (v : Vertex F) (r : ℕ) :
    stabilizer F v ≤ normalizer (V F v r : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (V F v r).map (MulAut.conj g).toMonoidHom = V F v r
  rw [← V_translate]
  rw [hg]

/-- The triangle inequality puts each ball generator in the opposite stabilizer. -/
theorem V_le_stabilizer (hgen : F false ⊔ F true = ⊤)
    (v w : Vertex F) {r : ℕ} (hd : (graph F).dist v w + r ≤ b F) :
    V F v r ≤ stabilizer F w := by
  apply iSup_le
  intro z
  apply iSup_le
  intro hz
  apply Z_le_stabilizer_of_dist_le_b F hgen z w
  have hz' := (mem_ball_iff F hgen v z r).mp hz
  have ht := (connected F hgen).dist_triangle (u := z) (v := v) (w := w)
  rw [SimpleGraph.dist_comm (u := z) (v := v)] at ht
  omega

/-- The elementary radius-one spans act quadratically on each other. -/
theorem V_mutual_quadratic [∀ i, Finite (F i)] (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hS : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (v w : Vertex F) (hb : 2 < b F) (hd : (graph F).dist v w + 1 ≤ b F) :
    ⁅⁅V F v 1, V F w 1⁆, V F v 1⁆ = ⊥ ∧
      ⁅⁅V F v 1, V F w 1⁆, V F w 1⁆ = ⊥ := by
  let := V_elementary F hgen hZ hS v (r := 1) (by simpa using hb)
  let := V_elementary F hgen hZ hS w (r := 1) (by simpa using hb)
  have hnw := (V_le_stabilizer F hgen v w hd).trans (stabilizer_normalizes_V F w 1)
  have hnv := (V_le_stabilizer F hgen w v (by rwa [SimpleGraph.dist_comm])).trans
    (stabilizer_normalizes_V F v 1)
  constructor
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (le_normalizer_iff_commutator_le_left.mp hnv).trans (le_centralizer _)
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (le_normalizer_iff_commutator_le_right.mp hnw).trans (le_centralizer _)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
