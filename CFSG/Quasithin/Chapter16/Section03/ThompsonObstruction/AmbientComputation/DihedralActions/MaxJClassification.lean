module
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.Products
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionData
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ActionConstruction
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.ComponentFamily
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.TailFamily
public import Stellmacher.ElementaryAbelianMaxProduct

/-!
# The T₀ maximum elementary family and compatible Thompson product

For either marked candidate w, the actual multiplication product identifies
T₀ with (T_C⟨w⟩) × T_L. Maximum-order elementary subgroups split across this
product. The component factor has exactly two maximum four-groups, which
generate T_L. Consequently J(T) = J(T_C⟨w⟩) T_L once RankGeometry has
placed the maximum family in T₀.

The constructed maximizing action and the exact tail-family calculation
discharge both inputs to this reduction. Every maximum elementary subgroup of
T₀ is a four-group of R times one of the two component four-groups times ⟨w⟩.
The final existence theorems construct these factors and the compatible
decomposition from Prepared and RankGeometry alone, retaining both source
action alternatives. No unrestricted omega subgroup is identified with J(T).
Construction of Prepared and RankGeometry remains with the source assembly.
Source: Aschbacher--Smith, 16.3.12, printed pp.1181--1182 / PDF pp.1198--1199.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

omit [Finite G] in
private theorem tail_centralizes_component (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    commutingSylow T L ⊔ zpowers w ≤ centralizer (componentSylow T L : Set G) :=
  sup_le (inf_le_right.trans (centralizer_le (show componentSylow T L ≤ L from inf_le_right)))
    (zpowers_le.mpr (candidate_mem_and_centralizes d hw).2)

/-- Every maximum elementary subgroup of T₀ is exactly a maximum tail subgroup
joined with one of the two marked component four-groups. -/
theorem smallGroup_maxFamily_iff (d : Prepared T z t L) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u)
    (e : componentSylow T L ≃* DihedralGroup 4) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (smallGroup d) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups (commutingSylow T L ⊔ zpowers w),
      ∃ i : Fin 2, A = B ⊔ componentFour (componentSylow T L) e i := by
  have hs : smallGroup d = (commutingSylow T L ⊔ zpowers w) ⊔ componentSylow T L := by
    rw [smallGroup_eq_candidate_join d hw, sup_right_comm]
  rw [hs, maxFamily_sup_iff_of_disjoint_of_commuting _ _
    (candidate_tail_disjoint_component d hw) (tail_centralizes_component d hw) A]
  constructor
  · rintro ⟨B, hB, C, hC, hA⟩
    obtain ⟨i, rfl⟩ := (component_maxFamily_iff _ e C).mp hC
    exact ⟨B, hB, i, hA⟩
  · rintro ⟨B, hB, i, hA⟩
    exact ⟨B, hB, _, (component_maxFamily_iff _ e _).mpr ⟨i, rfl⟩, hA⟩

/-- The full rank geometry is used only to pass from T to T₀; the internal
product and its maximum family give the remaining equality directly. -/
theorem maxJ_eq_tail_join (d : Prepared T z t L) (r : RankGeometry d) {w : G}
    (hw : w = d.marked.u ∨ w = t * d.marked.u) :
    elementaryAbelianMaxJ (T : Subgroup G) =
      elementaryAbelianMaxJ (commutingSylow T L ⊔ zpowers w) ⊔ componentSylow T L := by
  obtain ⟨e⟩ := r.component_dihedral
  rw [maxJ_eq_smallGroup d r.maximal_le, smallGroup_eq_candidate_join d hw,
    sup_right_comm (commutingSylow T L) (componentSylow T L) (zpowers w),
    elementaryAbelianMaxJ_sup_of_disjoint_of_commuting _ _
      (candidate_tail_disjoint_component d hw) (tail_centralizes_component d hw),
    component_maxJ _ e]

/-- The direct tail calculation is the only remaining maximum-family premise.
No unrestricted first-omega subgroup is substituted for the Thompson subgroup. -/
theorem maxJ_eq_candidate_join_of_tail (d : Prepared T z t L) (r : RankGeometry d)
    (a : ActionData d)
    (hTail : elementaryAbelianMaxJ (commutingSylow T L ⊔ zpowers a.w) = a.R ⊔ zpowers a.w) :
    elementaryAbelianMaxJ (T : Subgroup G) = a.R ⊔ componentSylow T L ⊔ zpowers a.w := by
  rw [maxJ_eq_tail_join d r a.candidate, hTail, sup_right_comm]

/-- The action output and intrinsic tail calculation assemble the compatible
source product, including its ambient multiplication formula. -/
theorem decomposition_of_tail_calculation (d : Prepared T z t L) (r : RankGeometry d)
    (a : ActionData d)
    (hTail : elementaryAbelianMaxJ (commutingSylow T L ⊔ zpowers a.w) = a.R ⊔ zpowers a.w) :
    Nonempty (Decomposition d) := by
  have hJ := maxJ_eq_candidate_join_of_tail d r a hTail
  obtain ⟨e, he⟩ := exists_candidate_product d a.candidate a.R a.R_le (a.centralizes_R d)
  exact ⟨{
    y := a.y
    rotation_le := a.rotation_le
    rotation_characteristic := a.rotation_characteristic
    rotation_index := a.rotation_index
    rotation_order := a.rotation_order
    reflection_generation := a.reflection_generation
    reflection_action := a.reflection_action
    w := a.w
    candidate := a.candidate
    maximizing := a.maximizing
    involution := a.involution
    R := a.R
    R_le := a.R_le
    dihedral := a.dihedral
    center_eq := a.center_eq
    alternative := a.alternative
    product := e.trans (MulEquiv.subgroupCongr hJ.symm)
    product_apply := he }⟩

/-- The exact tail-family classification propagates to every maximum elementary
subgroup of T₀ with its actual ambient inclusions. -/
theorem smallGroup_maxFamily_of_tail (d : Prepared T z t L) (a : ActionData d)
    (e : componentSylow T L ≃* DihedralGroup 4)
    (hTail : ∀ E : Subgroup G,
      E ∈ elementaryAbelianMaxSubgroups (commutingSylow T L ⊔ zpowers a.w) ↔
        ∃ B ∈ elementaryAbelianMaxSubgroups a.R, E = B ⊔ zpowers a.w)
    (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (smallGroup d) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups a.R, ∃ i : Fin 2,
        A = B ⊔ componentFour (componentSylow T L) e i ⊔ zpowers a.w := by
  rw [smallGroup_maxFamily_iff d a.candidate e A]
  constructor
  · rintro ⟨E, hE, i, hA⟩
    obtain ⟨B, hB, rfl⟩ := (hTail E).mp hE
    exact ⟨B, hB, i, hA.trans (sup_right_comm _ _ _)⟩
  · rintro ⟨B, hB, i, hA⟩
    exact ⟨B ⊔ zpowers a.w, (hTail _).mpr ⟨B, hB, rfl⟩, i,
      hA.trans (sup_right_comm _ _ _)⟩

/-- The exact T₀ family with the intrinsic tail calculation discharged. -/
theorem smallGroup_maxFamily (d : Prepared T z t L) (a : ActionData d)
    (e : componentSylow T L ≃* DihedralGroup 4) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (smallGroup d) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups a.R, ∃ i : Fin 2,
        A = B ⊔ componentFour (componentSylow T L) e i ⊔ zpowers a.w :=
  smallGroup_maxFamily_of_tail d a e (tail_maxFamily_iff d a) A

/-- Explicitly, the R factor ranges over its elementary four-groups. Thus this
classification has no residual maximum-family calculation in either factor. -/
theorem smallGroup_maxFamily_iff_four (d : Prepared T z t L) (a : ActionData d)
    (e : componentSylow T L ≃* DihedralGroup 4) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (smallGroup d) ↔
      ∃ B : Subgroup G, B ≤ a.R ∧ IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧
        ∃ i : Fin 2, A = B ⊔ componentFour (componentSylow T L) e i ⊔ zpowers a.w := by
  obtain ⟨n, hn, ⟨eR⟩⟩ := a.dihedral
  rw [smallGroup_maxFamily d a e A]
  constructor
  · rintro ⟨B, hB, i, hA⟩
    obtain ⟨hBR, hBe, hBc⟩ := (dihedral_maxFamily_iff a.R hn eR B).mp hB
    exact ⟨B, hBR, hBe, hBc, i, hA⟩
  · rintro ⟨B, hBR, hBe, hBc, i, hA⟩
    exact ⟨B, (dihedral_maxFamily_iff a.R hn eR B).mpr ⟨hBR, hBe, hBc⟩, i, hA⟩

/-- The direct maximum-family calculation gives the actual ambient J(T). -/
theorem maxJ_eq_candidate_join (d : Prepared T z t L) (r : RankGeometry d)
    (a : ActionData d) :
    elementaryAbelianMaxJ (T : Subgroup G) = a.R ⊔ componentSylow T L ⊔ zpowers a.w :=
  maxJ_eq_candidate_join_of_tail d r a (tail_maxJ d a)

/-- Constructed maximizing action, exact T₀ family, and compatible J(T) product,
with all factors in the classification and multiplication formula chosen together. -/
theorem exists_maxJ_classification (d : Prepared T z t L) (r : RankGeometry d) :
    ∃ (a : ActionData d) (e : componentSylow T L ≃* DihedralGroup 4),
      (∀ A : Subgroup G, A ∈ elementaryAbelianMaxSubgroups (smallGroup d) ↔
        ∃ B : Subgroup G, B ≤ a.R ∧ IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧
          ∃ i : Fin 2, A = B ⊔ componentFour (componentSylow T L) e i ⊔ zpowers a.w) ∧
      elementaryAbelianMaxJ (T : Subgroup G) = a.R ⊔ componentSylow T L ⊔ zpowers a.w ∧
      ∃ f : (a.R × componentSylow T L × zpowers a.w) ≃*
          elementaryAbelianMaxJ (T : Subgroup G),
        ∀ (x : a.R) (b : componentSylow T L) (c : zpowers a.w),
          (f (x, b, c) : G) = (x : G) * (b : G) * (c : G) := by
  obtain ⟨a⟩ := exists_actionData d r
  obtain ⟨e⟩ := r.component_dihedral
  have hJ := maxJ_eq_candidate_join d r a
  obtain ⟨f, hf⟩ := exists_candidate_product d a.candidate a.R a.R_le (a.centralizes_R d)
  exact ⟨a, e, smallGroup_maxFamily_iff_four d a e, hJ,
    f.trans (MulEquiv.subgroupCongr hJ.symm), hf⟩

/-- The full compatible decomposition required by 16.3.12 follows from the
prepared data and rank geometry, with no action or Thompson equality assumed. -/
theorem exists_decomposition (d : Prepared T z t L) (r : RankGeometry d) :
    Nonempty (Decomposition d) := by
  obtain ⟨a⟩ := exists_actionData d r
  exact decomposition_of_tail_calculation d r a (tail_maxJ d a)

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
