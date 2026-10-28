module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiCoreDichotomy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SuzukiIntersectionCommutator
public import Theory.GroupTheory.PGroup.CenterFreeGeneration

/-!
# The Suzuki middle-core product and original-parabolic commutators

For distinct neighbors x and y of m, write H = V_x ∩ V_y and
N = (Q_x ∩ Q_m) ∨ (Q_y ∩ Q_m). The proved index dichotomy gives either
N = Q_m or N = V_x ∨ (Q_m ∩ Q_y). In the latter case, [H,N] is normal
in the starred middle group and contained in Z_y. Minimality of Z_m and
the strict center orders force [H,N] = 1. Three-subgroups rotation and
the finite two-group center theorem then make H centralize Q_m, contrary
to the already proved Suzuki intersection noncentrality.

Thus Q_m = N. The literal source application discharges precisely the
product premise of source_suzuki_intersection_commutator, returning the
product together with all four original reduced/original commutator
identities. It retains the actual quotient markings and inclusion into
the original completion. The common Sylows, natural-center minimality
and orders, critical geometry and conjugated index data are genuine earlier
Chapter 8 inputs; the later binary and (12.9)/(13.1) assembly remains open.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
Part II, (12.1)(d--g), (12.3)(a--d), printed pp.178--180.
The proof was supplied and checked in Scratch/DriverSuzukiProductOct23.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] (F : Bool → Subgroup G) [∀ i, Finite (F i)]

/-- The bad seed formula forces the intersection to centralize the middle
core, using the natural center's minimality and the three-core generation. -/
theorem seed_alternative_centralizes_intersection
    (hQ : ∀ v, Q F v ≤ U F v)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    {x y m : Vertex F}
    (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (_hA : A ≤ stabilizer F m)
    (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m)
    (hz : center A = ⊥)
    (hVxQ : V F x 1 ≤ Q F m)
    (hVx : IsElementaryAbelian 2 (V F x 1))
    (hx : ⁅V F x 1,Q F x⁆ ≤ Z F x)
    (hy : ⁅V F y 1,Q F y⁆ ≤ Z F y)
    (hzx : Z F x ≤ Z F m) (hzy : Z F y ≤ Z F m)
    (hylt : ¬ Z F m ≤ Z F y)
    (hmin : ∀ D : Subgroup A, D.Normal → D ≤ (Z F m).subgroupOf A →
      D = ⊥ ∨ D = (Z F m).subgroupOf A)
    (hseed : (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) =
      V F x 1 ⊔ (Q F m ⊓ Q F y)) :
    V F x 1 ⊓ V F y 1 ≤ centralizer (Q F m : Set G) := by
  let H := V F x 1 ⊓ V F y 1
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  have hHQ : H ≤ Q F m := inf_le_left.trans hVxQ
  have hQA : Q F m ≤ A := le_sup_right.trans hgen.ge
  have hZA : Z F m ≤ A := ((hZ m).trans (map_subtype_le _)).trans hQA
  have hnH : A ≤ normalizer (H : Set G) := by
    rw [hgen]
    exact intersection_normalized F hQ hxm hym hx hy hzx hzy
  have hnN : A ≤ normalizer (N : Set G) :=
    middle_core_product_normalizer F hQ hxm hym A hgen
  have hZQ : Z F m ≤ centralizer (Q F m : Set G) :=
    fun z hz => ((mem_omegaCenterIn_iff _ _).mp (hZ m hz)).2.1
  have hnZy : Q F m ≤ normalizer (Z F y : Set G) :=
    (le_centralizer_iff.mp (hzy.trans hZQ)).trans (Subgroup.centralizer_le_normalizer _)
  have hHNle : ⁅H,N⁆ ≤ Z F y := by
    rw [commutator_comm, show N = V F x 1 ⊔ (Q F m ⊓ Q F y) from hseed]
    apply commutator_sup_le_of_relative_normal (Q F m) _ _ _ _ hnZy hVxQ inf_le_left
    · let := hVx
      have hzero : ⁅V F x 1,H⁆ = ⊥ :=
        commutator_eq_bot_iff_le_centralizer.mpr
          ((le_centralizer (H := V F x 1)).trans (centralizer_le inf_le_left))
      exact hzero.le.trans bot_le
    · rw [commutator_comm]
      exact (commutator_mono inf_le_right inf_le_right).trans hy
  have hnD : A ≤ normalizer (⁅H,N⁆ : Subgroup G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hnH hg),
      mem_normalizer_iff_map_conj_eq.mp (hnN hg)]
  have hDA : ⁅H,N⁆ ≤ A := hHNle.trans (hzy.trans hZA)
  have hHN : ⁅H,N⁆ = ⊥ := by
    let hn : (⁅H,N⁆.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hnD
    rcases hmin (⁅H,N⁆.subgroupOf A) hn (subgroupOf_mono A (hHNle.trans hzy)) with he | he
    · have hm := congrArg (Subgroup.map A.subtype) he
      simpa only [map_subgroupOf_eq_of_le hDA,Subgroup.map_bot] using hm
    · exfalso
      have hm := congrArg (Subgroup.map A.subtype) he
      rw [map_subgroupOf_eq_of_le hDA,map_subgroupOf_eq_of_le hZA] at hm
      exact hylt (hm.ge.trans hHNle)
  have hadj_normal {v w : Vertex F} (hvw : (graph F).Adj v w) :
      Q F v ≤ normalizer (Q F w : Set G) :=
    ((hQ v).trans ((ballKernel_one_le_edge F hvw).trans inf_le_right)).trans
      ((stabilizer F w).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F w))))
  have hc {v : Vertex F} (hv : (graph F).Adj v m) :
      ⁅Q F m,Q F v⁆ ≤ Q F v ⊓ Q F m :=
    le_inf (le_normalizer_iff_commutator_le_right.mp (hadj_normal hv.symm))
      (le_normalizer_iff_commutator_le_left.mp (hadj_normal hv))
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  apply Subgroup.centralizes_core_of_centralizing_defect
    A (Q F m) H N (Q F x) (Q F y) (Z F m)
    (pCore_isPGroup.map (stabilizer F m).subtype) hHQ hQA hgen hz hZQ
  · exact ((commutator_mono inf_le_left le_rfl).trans hx).trans hzx
  · exact ((commutator_mono inf_le_right le_rfl).trans hy).trans hzy
  · exact (hc hxm).trans le_sup_left
  · exact (hc hym).trans le_sup_right
  · exact hHN

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile


namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
open Subgroup.CosetGeometry.RankTwo Reduction
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal source consumer with the former middle-core-product input discharged. -/
theorem source_suzuki_product_and_intersection_commutator
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    {a x σ : Vertex (reducedFamily L S)}
    (hxadj : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) i) x)
    (hne : x ≠ base (reducedFamily L S) (!i))
    (T R : Sylow 2 (star L S i))
    (hT : (T : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hR : (R : Subgroup (star L S i)).map (star L S i).subtype =
      Q (reducedFamily L S) x ⊔ Q (reducedFamily L S) (base (reducedFamily L S) i))
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) k)
    (hz : center (star L S i) = ⊥)
    (hcard : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) i)) = Nat.card k ^ 2)
    (hcardy : Nat.card (Z (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    (hzx : Z (reducedFamily L S) x ≤ Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcommx : ⁅V (reducedFamily L S) x 1, Q (reducedFamily L S) x⁆ ≤ Z (reducedFamily L S) x)
    (hcommy : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcross : ⁅V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1 ⊓ Q (reducedFamily L S) σ,
      V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))⁆ = ⊥)
    (hsmall : (Q (reducedFamily L S) σ).relIndex
      (V (reducedFamily L S) (base (reducedFamily L S) (!i)) 1) ≤ Nat.card k)
    (hactor : (Q (reducedFamily L S) (base (reducedFamily L S) i)).relIndex
      (V (reducedFamily L S) σ 1 ⊓ Q (reducedFamily L S) (base (reducedFamily L S) (!i))) = Nat.card k)
    {n : ℕ} (hn : 0 < n)
    (eSuz : (L (if !i then 1 else 0) ⧸ pCore 2 (L (if !i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (hfield : Nat.card k = 2 ^ (2 * n + 1))
    (Ry : Sylow 2 (star L S (!i)))
    (hRy : (Ry : Subgroup (star L S (!i))).map (star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hc : IsCriticalPair (reducedFamily L S) a (base (reducedFamily L S) (!i)))
    (hxa : (graph (reducedFamily L S)).Adj x a)
    (hmin : ∀ N : Subgroup (star L S i), N.Normal →
      N ≤ (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i) →
      N = ⊥ ∨ N = (Z (reducedFamily L S) (base (reducedFamily L S) i)).subgroupOf (star L S i)) :
    let F := reducedFamily L S
    let H := V F x 1 ⊓ V F (base F (!i)) 1
    Q F (base F i) = (Q F x ⊓ Q F (base F i)) ⊔
      (Q F (base F (!i)) ⊓ Q F (base F i)) ∧
    ⁅H, Q F (base F i)⁆ = Z F (base F i) ∧
      ⁅H.map (G₀ L S).subtype, (parabolic L S (if i then 1 else 0)).pCoreIn 2⁆ =
        (Z F (base F i)).map (G₀ L S).subtype ∧
      V F (base F (!i)) 1 = ⁅V F (base F (!i)) 1, star L S (!i)⁆ ∧
      (V F (base F (!i)) 1).map (G₀ L S).subtype =
        ⁅(V F (base F (!i)) 1).map (G₀ L S).subtype,
          starredParabolic L S (if !i then 1 else 0)⁆ := by
  let F := reducedFamily L S
  let m := base F i
  let y := base F (!i)
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  have hZ := fun v => (source_Z_Q_U (reduced_triple h) v).1
  have hQ := fun v => (source_Z_Q_U (reduced_triple h) v).2
  have hadj : (graph F).Adj m y :=
    ⟨by change i ≠ !i; cases i <;> decide, Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hnot := source_suzuki_intersection_not_central h i hb hxadj hne T R hT hR e
    hz hcard hcardy hzx hzy hcommx hcommy.le hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa
  have hgen : star L S i = (Q F x ⊔ Q F y) ⊔ Q F m := by
    have hh := star_three_core_generation h i hxadj hne T R hT hR
    simpa only [sup_comm, sup_left_comm, sup_assoc] using hh
  have hylt : ¬ Z F m ≤ Z F y := by
    intro hle
    let : Finite (Z F y) := Finite.of_injective
      (inclusion (Z_le_stabilizer F y)) (inclusion_injective _)
    have hlecard := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)
    change Nat.card (Z F m) ≤ Nat.card (Z F y) at hlecard
    rw [hcard,hcardy] at hlecard
    have hq : 1 < Nat.card k := Finite.one_lt_card
    nlinarith
  have hcases : N = Q F m ∨
      N = V F x 1 ⊔ (Q F m ⊓ Q F y) ∧ N.relIndex (Q F m) = 2 ^ (2 * n + 1) := by
    have hh := (source_suzuki_middle_core_product_or_seed (k := k) h (!i) hb hc hxa
      (by simpa only [Bool.not_not] using hxadj.symm) hn eSuz
      (by cases i <;> exact e) Ry
      (by simpa only [Bool.not_not] using hRy)
      (by cases i <;> exact T) (by cases i <;> exact R)
      (by cases i <;> exact hT)
      (by cases i <;> exact hR)).2
    simpa only [Bool.not_not] using hh
  have hprod : Q F m = N := by
    rcases hcases with he | ⟨he,_⟩
    · exact he.symm
    · exfalso
      apply hnot
      exact seed_alternative_centralizes_intersection F hQ hZ hxadj.symm hadj.symm
        (star L S i) (star_le_stabilizer i) hgen hz
        (V_le_neighbor_Q F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb hxadj.symm)
        (V_elementary F (reduced_triple h).generate hZ (reduced_kernel_sylow h) hb x)
        hcommx hcommy.le hzx hzy hylt hmin he
  refine ⟨hprod, ?_⟩
  exact source_suzuki_intersection_commutator h i hb hxadj hne T R hT hR e
    hz hcard hcardy hzx hzy hcommx hcommy hcross hsmall hactor hn eSuz hfield Ry hRy hc hxa
    hprod hmin

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile.ReducedLayer
