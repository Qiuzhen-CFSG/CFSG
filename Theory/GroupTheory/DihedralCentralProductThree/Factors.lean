module
public import Theory.GroupTheory.DihedralCentralProductThree.Marked
public import Theory.GroupTheory.DihedralCentralProductThree.Splitting

/-!
# Intrinsic construction of three dihedral factors

An elementary sixteen in an extraspecial group of order 128 yields successive
dihedral splittings with centralizers of orders 32 and 8. The elementary
subgroups retained in the centralizers have orders 8 and 4: the splitting
lower bound and the extraspecial elementary-subgroup upper bound coincide.
The last order-eight group is therefore dihedral.

Composing the factor inclusions gives three faithful, commuting maps from
D₈ whose images generate the original group. Their central rotations are
the same nonidentity central element, since the center has order two.
No plus-type classification or hyperbolic-basis hypothesis is assumed.
Source: the intrinsic recognition underlying Aschbacher–Smith 15.3.58(2),
printed pp.1148–1149.
-/

namespace DihedralCentralProductThree
open Subgroup DihedralGroup

private theorem factor_maps_of_nested_splittings
    {P : Type*} [Group P] (D₁ : Subgroup P) (e₁ : D₁ ≃* DihedralGroup 4)
    (hg₁ : D₁ ⊔ centralizer (D₁ : Set P) = ⊤)
    (D₂ : Subgroup (centralizer (D₁ : Set P))) (e₂ : D₂ ≃* DihedralGroup 4)
    (hg₂ : D₂ ⊔ centralizer (D₂ : Set (centralizer (D₁ : Set P))) = ⊤)
    (e₃ : centralizer (D₂ : Set (centralizer (D₁ : Set P))) ≃* DihedralGroup 4) :
    ∃ f : Fin 3 → DihedralGroup 4 →* P,
      (∀ i, Function.Injective (f i)) ∧
      (Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) ∧
      (⨆ i, (f i).range) = ⊤ := by
  let C₁ := centralizer (D₁ : Set P)
  let C₂ := centralizer (D₂ : Set C₁)
  let f₁ : DihedralGroup 4 →* P := D₁.subtype.comp e₁.symm.toMonoidHom
  let f₂ : DihedralGroup 4 →* P := C₁.subtype.comp (D₂.subtype.comp e₂.symm.toMonoidHom)
  let f₃ : DihedralGroup 4 →* P := C₁.subtype.comp (C₂.subtype.comp e₃.symm.toMonoidHom)
  let f : Fin 3 → DihedralGroup 4 →* P := ![f₁, f₂, f₃]
  have h₁₂ (x y : DihedralGroup 4) : Commute (f₁ x) (f₂ y) :=
    (e₂.symm y : C₁).property _ (e₁.symm x).property
  have h₁₃ (x y : DihedralGroup 4) : Commute (f₁ x) (f₃ y) :=
    (e₃.symm y : C₁).property _ (e₁.symm x).property
  have h₂₃ (x y : DihedralGroup 4) : Commute (f₂ x) (f₃ y) :=
    congrArg Subtype.val ((e₃.symm y).property _ (e₂.symm x).property)
  have hr₁ : f₁.range = D₁ := by simp [f₁, MonoidHom.range_comp, ← MonoidHom.range_eq_map]
  have hr₂ : f₂.range = D₂.map C₁.subtype := by simp [f₂, MonoidHom.range_comp, ← MonoidHom.range_eq_map]
  have hr₃ : f₃.range = C₂.map C₁.subtype := by simp [f₃, MonoidHom.range_comp, ← MonoidHom.range_eq_map]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact D₁.subtype_injective.comp e₁.symm.injective
    · exact C₁.subtype_injective.comp (D₂.subtype_injective.comp e₂.symm.injective)
    · exact C₁.subtype_injective.comp (C₂.subtype_injective.comp e₃.symm.injective)
  · intro i j hij x y
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    · exact h₁₂ x y
    · exact h₁₃ x y
    · exact (h₁₂ y x).symm
    · exact h₂₃ x y
    · exact (h₁₃ y x).symm
    · exact (h₂₃ y x).symm
  · have hh : (⨆ i, (f i).range) = f₁.range ⊔ (f₂.range ⊔ f₃.range) := by
      apply le_antisymm
      · apply iSup_le
        intro i
        fin_cases i
        · exact le_sup_left
        · exact le_sup_of_le_right le_sup_left
        · exact le_sup_of_le_right le_sup_right
      · exact sup_le (le_iSup (fun i => (f i).range) 0)
          (sup_le (le_iSup (fun i => (f i).range) 1) (le_iSup (fun i => (f i).range) 2))
    rw [hh, hr₁, hr₂, hr₃, ← Subgroup.map_sup, hg₂]
    simpa only [← MonoidHom.range_eq_map, C₁.range_subtype] using hg₁

private theorem aligned_central_rotations
    {P : Type*} [Group P] [IsExtraspecial 2 P]
    (f : Fin 3 → DihedralGroup 4 →* P)
    (hinj : ∀ i, Function.Injective (f i))
    (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hg : (⨆ i, (f i).range) = ⊤) :
    ∀ i, f i (r 2) = f 0 (r 2) := by
  have hcent (i : Fin 3) : f i (r 2) ∈ center P := by
    have hle : (⨆ j, (f j).range) ≤ centralizer ({f i (r 2)} : Set P) := by
      apply iSup_le
      intro j x hx
      obtain ⟨y, rfl⟩ := hx
      apply mem_centralizer_singleton_iff.mpr
      by_cases hij : j = i
      · subst j
        simpa only [map_mul] using congrArg (f i) (Subgroup.mem_center_iff.mp r_two_central y)
      · exact hc hij y (r 2)
    rw [hg] at hle
    exact mem_center_iff.mpr (fun x => mem_centralizer_singleton_iff.mp (hle (mem_top x)))
  have hne (i : Fin 3) : f i (r 2) ≠ 1 := by
    intro h
    exact (by decide : (r 2 : DihedralGroup 4) ≠ 1)
      (hinj i (h.trans (map_one (f i)).symm))
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
    (IsExtraspecial.center_order_p 2 P)
  intro i
  exact congrArg Subtype.val ((hz ⟨_, hcent i⟩ (fun h => hne i (congrArg Subtype.val h))).trans
    (hz ⟨_, hcent 0⟩ (fun h => hne 0 (congrArg Subtype.val h))).symm)

/-- Three faithful, commuting dihedral factors constructed from an elementary sixteen. -/
public theorem exists_dihedral_factor_maps
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 128) (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 16) (hZA : center P ≤ A) :
    ∃ f : Fin 3 → DihedralGroup 4 →* P,
      (∀ i, Function.Injective (f i)) ∧
      (Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) ∧
      (∀ i, f i (r 2) = f 0 (r 2)) ∧ (⨆ i, (f i).range) = ⊤ := by
  obtain ⟨D₁, ⟨e₁⟩, hg₁, hC₁, hA₁, hZA₁, hc₁, ha₁⟩ :=
    exists_dihedral_split A hZA (by omega) (by omega)
  let C₁ := centralizer (D₁ : Set P)
  let A₁ := A.subgroupOf C₁
  let : IsExtraspecial 2 C₁ := hC₁
  let : IsElementaryAbelian 2 A₁ := hA₁
  have hC₁card : Nat.card C₁ = 32 := by
    change Nat.card P = 4 * Nat.card C₁ at hc₁
    omega
  have hA₁card : Nat.card A₁ = 8 := by
    have hb := extraspecial_two_elementary_card_sq_le A₁ hZA₁
    rw [hC₁card] at hb
    change Nat.card A ≤ 2 * Nat.card A₁ at ha₁
    rw [hA] at ha₁
    nlinarith
  obtain ⟨D₂, ⟨e₂⟩, hg₂, hC₂, hA₂, hZA₂, hc₂, ha₂⟩ :=
    exists_dihedral_split A₁ hZA₁ (by omega) (by omega)
  let C₂ := centralizer (D₂ : Set C₁)
  let A₂ := A₁.subgroupOf C₂
  let : IsExtraspecial 2 C₂ := hC₂
  let : IsElementaryAbelian 2 A₂ := hA₂
  have hC₂card : Nat.card C₂ = 8 := by
    change Nat.card C₁ = 4 * Nat.card C₂ at hc₂
    omega
  have hA₂card : Nat.card A₂ = 4 := by
    have hb := extraspecial_two_elementary_card_sq_le A₂ hZA₂
    rw [hC₂card] at hb
    change Nat.card A₁ ≤ 2 * Nat.card A₂ at ha₂
    rw [hA₁card] at ha₂
    nlinarith
  obtain ⟨e₃⟩ := dihedral_of_elementary_four hC₂card A₂ hA₂card
  obtain ⟨f, hinj, hc, hg⟩ := factor_maps_of_nested_splittings D₁ e₁ hg₁ D₂ e₂ hg₂ e₃
  exact ⟨f, hinj, hc, aligned_central_rotations f hinj hc hg, hg⟩

end DihedralCentralProductThree
