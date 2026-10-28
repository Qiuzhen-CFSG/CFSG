module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.IntersectionGeometry

/-!
# The binary middle-core product

The intersection of two adjacent cores is normalized by the full edge.
Consequently a locally transitive subgroup of the middle stabilizer tests
normality in the whole stabilizer. If two such intersections coincide, the
three cores generating the local group normalize that intersection.

The earlier nonnormality assertion therefore separates the two intersections.
When each has index two in the middle core, multiplicativity of relative
indices makes their join the entire core. Mutual normalization identifies
this join with the literal ordered product. Conjugation in the middle vertex
transports the index to the second intersection.

Source: DGS85, *Groups and Graphs*, (6.5), (12.1)(c), and the first displayed
line on printed p.180. The concrete order-ten quotient and original-group
application are supplied by `DihedralCoreProduct`. The order-twenty Suzuki
row and nonbinary Suzuki row are not included in the index-two argument.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

private theorem sup_eq_of_two_indices (A B Q : Subgroup G)
    (hAQ : A ≤ Q) (hBQ : B ≤ Q) (hiA : A.relIndex Q = 2)
    (hiB : B.relIndex Q = 2) (hne : A ≠ B) : A ⊔ B = Q := by
  have hn : ¬ B ≤ A := by
    intro hBA
    have hm := relIndex_mul_relIndex B A Q hBA hAQ
    rw [hiA, hiB] at hm
    exact hne (le_antisymm (relIndex_eq_one.mp (by omega : B.relIndex A = 1)) hBA)
  have hm := relIndex_mul_relIndex A (A ⊔ B) Q le_sup_left (sup_le hAQ hBQ)
  rw [hiA] at hm
  have hn' : A.relIndex (A ⊔ B) ≠ 1 := fun he =>
    hn (le_sup_right.trans (relIndex_eq_one.mp he))
  have hi : (A ⊔ B).relIndex Q = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hn' hh.2).elim
  exact le_antisymm (sup_le hAQ hBQ) (relIndex_eq_one.mp hi)

/-- The edge normalizes its two core intersection. A locally transitive
subgroup therefore tests normality in the full vertex stabilizer. -/
theorem core_intersection_normalizer_transfer
    (F : Bool → Subgroup G) {x m : Vertex F} (hxm : (graph F).Adj m x)
    (A : Subgroup G) (hA : A ≤ stabilizer F m)
    (htrans : ∀ y, (graph F).Adj m y → ∃ g ∈ A, g • x = y) :
    stabilizer F m ≤ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G) ↔
      A ≤ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G) := by
  refine ⟨fun hn => hA.trans hn, ?_⟩
  intro hn g hg
  have hmg : (graph F).Adj m (g • x) := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).map_adj_iff.mpr hxm
    change (graph F).Adj (g • m) (g • x) at hh
    rwa [show g • m = m from hg] at hh
  obtain ⟨a, ha, hax⟩ := htrans (g • x) hmg
  have hcm : a⁻¹ * g ∈ stabilizer F m :=
    (stabilizer F m).mul_mem ((stabilizer F m).inv_mem (hA ha)) hg
  have hcx : a⁻¹ * g ∈ stabilizer F x := by
    change (a⁻¹ * g) • x = x
    rw [mul_smul, ← hax, inv_smul_smul]
  have hnorm (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set G) :=
    (stabilizer F v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F v)))
  have hcn : a⁻¹ * g ∈ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hnorm x hcx, hnorm m hcm⟩
  have hh := (normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G)).mul_mem (hn ha) hcn
  simpa only [mul_inv_cancel_left] using hh

/-- The binary middle-core product follows from its two index-two intersections
and the earlier relative nonnormality assertion. -/
theorem middle_core_product_of_index_two
    (F : Bool → Subgroup G)
    (hQ : ∀ v, Q F v ≤ U F v)
    {x y m : Vertex F} (hxm : (graph F).Adj x m) (hym : (graph F).Adj y m)
    (A : Subgroup G) (hgen : A = (Q F x ⊔ Q F y) ⊔ Q F m)
    (hnot : ¬ A ≤ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G))
    (hx : (Q F x ⊓ Q F m).relIndex (Q F m) = 2)
    (hy : (Q F y ⊓ Q F m).relIndex (Q F m) = 2) :
    Q F m = (Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) ∧
      (Q F m : Set G) = ((Q F x ⊓ Q F m : Subgroup G) : Set G) * ((Q F y ⊓ Q F m : Subgroup G) : Set G) := by
  have hn (v : Vertex F) : stabilizer F v ≤ normalizer (Q F v : Set G) :=
    (stabilizer F v).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (stabilizer F v)))
  have hnAdj {v w : Vertex F} (hv : (graph F).Adj v w) :
      Q F v ≤ normalizer (Q F w : Set G) :=
    ((hQ v).trans ((ballKernel_one_le_edge F hv).trans inf_le_right)).trans (hn w)
  have hnX : Q F x ≤ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G) :=
    (le_inf (Q F x).le_normalizer (hnAdj hxm)).trans inf_normalizer_le_normalizer_inf
  have hnY : Q F y ≤ normalizer ((Q F y ⊓ Q F m : Subgroup G) : Set G) :=
    (le_inf (Q F y).le_normalizer (hnAdj hym)).trans inf_normalizer_le_normalizer_inf
  have hnM : Q F m ≤ normalizer ((Q F x ⊓ Q F m : Subgroup G) : Set G) :=
    (le_inf (hnAdj hxm.symm) (Q F m).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hne : Q F x ⊓ Q F m ≠ Q F y ⊓ Q F m := by
    intro he
    apply hnot
    rw [hgen]
    exact sup_le (sup_le hnX (by rw [he]; exact hnY)) hnM
  have he := (sup_eq_of_two_indices _ _ _ inf_le_right inf_le_right hx hy hne).symm
  refine ⟨he, ?_⟩
  calc
    (Q F m : Set G) = (((Q F x ⊓ Q F m) ⊔ (Q F y ⊓ Q F m) : Subgroup G) : Set G) := congrArg (fun H : Subgroup G => (H : Set G)) he
    _ = _ := coe_mul_of_right_le_normalizer_left _ _
      ((show Q F y ⊓ Q F m ≤ Q F m from inf_le_right).trans hnM)

/-- Conjugating within the middle vertex preserves the literal core-intersection index. -/
theorem middle_core_intersection_index_conjugate
    (F : Bool → Subgroup G) {x y m : Vertex F} (g : G)
    (hgm : g • m = m) (hgx : g • x = y) :
    (Q F y ⊓ Q F m).relIndex (Q F m) = (Q F x ⊓ Q F m).relIndex (Q F m) := by
  have he := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (Q F x ⊓ Q F m) (Q F m) (MulAut.conj g).injective
  rw [map_inf _ _ _ (MulAut.conj g).injective, ← Q_translate, ← Q_translate, hgx, hgm] at he
  exact he
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
