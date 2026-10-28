module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.MiddleCoreProduct
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Normality of the proposed middle-core product

For two neighbors x and y of m, put N = (Q_x ∩ Q_m)(Q_y ∩ Q_m).
Adjacent cores normalize one another. Their intersection factors are normal
in Q_m, so N is a subgroup, and commutator bounds show that all three cores
normalize it. Under the earlier three-core generation equation, N is thus
normal in the middle local group. If [Q_m,Q_m] lies in N, then [Q_m,L_m]
lies in N as well.

This isolates the central quotient that must be eliminated to prove the
product on DGS85, Groups and Graphs, printed p.180, proof of (12.3).
The nonbinary Suzuki application in SuzukiCoreQuotient derives the internal
commutator bound from the already proved first index and its Sylow-center
marking. Normality here does not assert N = Q_m.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem sup_normalizes_core_product (X Y Q : Subgroup G)
    (hXQ : X ≤ normalizer (Q : Set G)) (hQX : Q ≤ normalizer (X : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G)) (hQY : Q ≤ normalizer (Y : Set G)) :
    (X ⊔ Y) ⊔ Q ≤ normalizer (((X ⊓ Q) ⊔ (Y ⊓ Q) : Subgroup G) : Set G) := by
  let N := (X ⊓ Q) ⊔ (Y ⊓ Q)
  have hnQ : Q ≤ normalizer (N : Set G) :=
    (le_inf ((le_inf hQX Q.le_normalizer).trans inf_normalizer_le_normalizer_inf)
      ((le_inf hQY Q.le_normalizer).trans inf_normalizer_le_normalizer_inf)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnX : X ≤ normalizer ((X ⊓ Q : Subgroup G) : Set G) :=
    (le_inf X.le_normalizer hXQ).trans inf_normalizer_le_normalizer_inf
  have hnY : Y ≤ normalizer ((Y ⊓ Q : Subgroup G) : Set G) :=
    (le_inf Y.le_normalizer hYQ).trans inf_normalizer_le_normalizer_inf
  have hX : ⁅N, X⁆ ≤ N :=
    commutator_sup_le_of_relative_normal Q _ _ X N hnQ inf_le_right inf_le_right
      ((le_normalizer_iff_commutator_le_left.mp hnX).trans le_sup_left)
      ((commutator_mono inf_le_right le_rfl).trans
        ((le_inf (le_normalizer_iff_commutator_le_right.mp hQX)
          (le_normalizer_iff_commutator_le_left.mp hXQ)).trans le_sup_left))
  have hY : ⁅N, Y⁆ ≤ N :=
    commutator_sup_le_of_relative_normal Q _ _ Y N hnQ inf_le_right inf_le_right
      ((commutator_mono inf_le_right le_rfl).trans
        ((le_inf (le_normalizer_iff_commutator_le_right.mp hQY)
          (le_normalizer_iff_commutator_le_left.mp hYQ)).trans le_sup_right))
      ((le_normalizer_iff_commutator_le_left.mp hnY).trans le_sup_right)
  exact sup_le (sup_le (le_normalizer_iff_commutator_le_left.mpr hX)
    (le_normalizer_iff_commutator_le_left.mpr hY)) hnQ

private theorem adjacent_core_normalizes (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v) {v w : Vertex F} (hvw : (graph F).Adj v w) :
    Q F v ≤ normalizer (Q F w : Set G) :=
  ((hQ v).trans ((ballKernel_one_le_edge F hvw).trans inf_le_right)).trans
    ((stabilizer F w).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F w))))

/-- The join of the two intersections is their literal ordered product. -/
theorem middle_core_product_as_set (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v) {x y m : Vertex F}
    (hxm : (graph F).Adj x m) :
    (((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) : Subgroup G) : Set G) =
      ((Q F x ⊓ Q F m : Subgroup G) : Set G) *
        ((Q F y ⊓ Q F m : Subgroup G) : Set G) :=
  coe_mul_of_right_le_normalizer_left _ _
    ((show Q F y ⊓ Q F m ≤ Q F m from inf_le_right).trans
      ((le_inf (adjacent_core_normalizes F hQ hxm.symm) (Q F m).le_normalizer).trans
        inf_normalizer_le_normalizer_inf))

/-- The proposed middle-core product is relatively normal before proving that it is full. -/
theorem middle_core_product_normalizer (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m) :
    A ≤ normalizer (((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) : Subgroup G) : Set G) := by
  rw [hgen]
  exact sup_normalizes_core_product _ _ _ (adjacent_core_normalizes F hQ hxm)
    (adjacent_core_normalizes F hQ hxm.symm) (adjacent_core_normalizes F hQ hym)
    (adjacent_core_normalizes F hQ hym.symm)

/-- The middle-core commutator is absorbed by the product once its own derived subgroup is. -/
theorem middle_core_commutator_le_product (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m)
    (hderived : ⁅Q F m, Q F m⁆ ≤ (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)) :
    ⁅Q F m, A⁆ ≤ (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) := by
  let N := (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m)
  have hn := middle_core_product_normalizer F hQ hxm hym A hgen
  have hc {v : Vertex F} (hv : (graph F).Adj v m) :
      ⁅Q F v, Q F m⁆ ≤ Q F v ⊓ Q F m :=
    le_inf (le_normalizer_iff_commutator_le_left.mp (adjacent_core_normalizes F hQ hv.symm))
      (le_normalizer_iff_commutator_le_right.mp (adjacent_core_normalizes F hQ hv))
  rw [commutator_comm, hgen]
  exact commutator_sup_le_of_relative_normal A _ _ _ N hn
    (le_sup_left.trans hgen.ge) (le_sup_right.trans hgen.ge)
    (commutator_sup_le_of_relative_normal A _ _ _ N hn
      ((le_sup_left.trans le_sup_left).trans hgen.ge)
      ((le_sup_right.trans le_sup_left).trans hgen.ge)
      ((hc hxm).trans le_sup_left) ((hc hym).trans le_sup_right)) hderived

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
