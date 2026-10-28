module
public import Stellmacher.ElementaryAbelianMaxDihedral
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary ranks and generation in an elementary-by-dihedral group

A maximum elementary subgroup of E × D consists of E and a four-group
of the dihedral factor. Its order is twice the order of the center.
The four-groups generate D, so the elementary Thompson subgroup is the
whole product. The ambient versions retain the supplied subgroup embedding.

Source application: Aschbacher–Smith C.6.4, printed pp.168–169. These
formulas show that every dihedral overgroup of the marked R has the same
center and that the original Q remains maximum elementary.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G E : Type*} [Group G] [Group E] [Finite E]
  [IsElementaryAbelian 2 E]

private theorem elementary_top_max :
    (⊤ : Subgroup E) ∈ elementaryAbelianMaxSubgroups ⊤ :=
  ⟨le_rfl, IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype
    (⊤ : Subgroup E).subtype_injective, fun _ _ _ => card_le_of_le le_top⟩

private theorem elementary_max_eq_top (A : Subgroup E)
    (hA : A ∈ elementaryAbelianMaxSubgroups ⊤) : A = ⊤ :=
  eq_of_le_of_card_ge le_top (hA.2.2 ⊤ le_rfl elementary_top_max.2.1)

omit [Finite E] in
private theorem product_center_card {n : ℕ} (hn : 2 ≤ n) :
    Nat.card (center (E × DihedralGroup (2 ^ n))) = Nat.card E * 2 := by
  rw [Subgroup.center_prod, center_eq_top,
    Nat.card_congr (prodEquiv (⊤ : Subgroup E) (center (DihedralGroup (2 ^ n)))).toEquiv,
    Nat.card_prod, Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv,
    DihedralGroup.center_card_of_equiv hn (MulEquiv.refl _)]

/-- Maximum elementary subgroups have twice the order of the center. -/
theorem elementary_dihedral_max_card {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* E × DihedralGroup (2 ^ n)) (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups ⊤) :
    Nat.card A = 2 * Nat.card (center G) := by
  have hm := (maxFamily_map_injective_iff e.toMonoidHom e.injective ⊤ A).mpr hA
  rw [map_top_of_surjective _ e.surjective, ← top_prod_top] at hm
  obtain ⟨B,hB,C,hC,heq⟩ := maxFamily_prod_iff.mp hm
  have hBtop := elementary_max_eq_top B hB
  have hCc := (dihedral_maxFamily_iff_card_four hn C).mp hC |>.2
  rw [← card_map_of_injective (f := e.toMonoidHom) e.injective, heq, hBtop,
    Nat.card_congr (prodEquiv (⊤ : Subgroup E) C).toEquiv,
    Nat.card_prod, Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv, hCc,
    Nat.card_congr (centerCongr e).toEquiv, product_center_card hn]
  omega

/-- The center bounds the order of every elementary subgroup. -/
theorem elementary_dihedral_card_le {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* E × DihedralGroup (2 ^ n)) (A : Subgroup G)
    (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card (center G) := by
  let : Finite G := Finite.of_equiv (E × DihedralGroup (2 ^ n)) e.symm.toEquiv
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty (⊤ : Subgroup G)
  exact (hB.2.2 A le_top hA).trans_eq (elementary_dihedral_max_card hn e B hB)

/-- The maximum elementary subgroups generate an elementary-by-dihedral group. -/
theorem elementary_dihedral_maxJ {n : ℕ} (hn : 2 ≤ n)
    (e : G ≃* E × DihedralGroup (2 ^ n)) :
    elementaryAbelianMaxJ (⊤ : Subgroup G) = ⊤ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [← elementaryAbelianMaxJ_map_injective e.toMonoidHom e.injective,
    map_top_of_surjective _ e.surjective, ← top_prod_top, elementaryAbelianMaxJ_prod,
    dihedral_maxJ_top hn]
  have hE : elementaryAbelianMaxJ (⊤ : Subgroup E) = ⊤ :=
    top_unique (le_sSup elementary_top_max)
  rw [hE]

/-- The cardinality formula at the original ambient embedding. -/
theorem elementary_dihedral_max_card_ambient (M : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : M ≃* E × DihedralGroup (2 ^ n)) (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups M) :
    Nat.card A = 2 * Nat.card (center M) := by
  obtain ⟨B,hB,rfl⟩ := (maxFamily_equiv_iff M (MulEquiv.refl M) A).mp hA
  change Nat.card (B.map M.subtype) = _
  rw [card_map_of_injective M.subtype_injective]
  exact elementary_dihedral_max_card hn e B hB

/-- The elementary-order bound at the original ambient embedding. -/
theorem elementary_dihedral_card_le_ambient (M : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : M ≃* E × DihedralGroup (2 ^ n)) (A : Subgroup G)
    (hAM : A ≤ M) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 2 * Nat.card (center M) := by
  have hb := elementary_dihedral_card_le hn e (A.subgroupOf M) (hA.subgroupOf hAM)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv] at hb

/-- Ambient maximum elementary generation preserves the literal subgroup. -/
theorem elementary_dihedral_maxJ_ambient (M : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : M ≃* E × DihedralGroup (2 ^ n)) : elementaryAbelianMaxJ M = M := by
  have h := congrArg (fun A : Subgroup M => A.map M.subtype) (elementary_dihedral_maxJ hn e)
  simpa only [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,
    ← MonoidHom.range_eq_map, range_subtype] using h

end Theory.GroupTheory
