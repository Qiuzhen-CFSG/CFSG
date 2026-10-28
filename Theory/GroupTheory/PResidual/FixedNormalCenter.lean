module
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Central points of a residual-fixed normal p-subgroup

A nontrivial normal p-subgroup fixed by the p-residual meets the ambient
center nontrivially. A central point for a Sylow subgroup is fixed by the
residual as well, and those two subgroups generate the group. The image
version preserves the chosen subgroup and the literal homomorphism.

Source application: the first nonsolvable reduction of Aschbacher--Smith
E.2.17, where the original V has nontrivial image in the center of M/J.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A residual-fixed normal p-subgroup contains an ambient central point. -/
theorem exists_nontrivial_center_mem_normal_of_residual_centralizes
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) (A : Subgroup G) [A.Normal]
    (hA : IsPGroup p A) (hne : A ≠ ⊥)
    (hR : pResidual p G ≤ centralizer (A : Set G)) :
    ∃ a ∈ A, a ≠ 1 ∧ a ∈ center G := by
  have hAT : A ≤ T := hA.le_sylow_of_normal T
  let e := subgroupOfEquivOfLe hAT
  let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hne
  let : Nontrivial (A.subgroupOf (T : Subgroup G)) := e.toEquiv.nontrivial
  let : Fact (IsPGroup p T) := ⟨T.isPGroup'⟩
  obtain ⟨x, hx, hxc⟩ := exists_nontrivial_center_mem_normal (A.subgroupOf (T : Subgroup G)) (p := p)
  let a : G := x.val.val
  have ha : a ∈ A := x.property
  have hane : a ≠ 1 := by
    intro h
    apply hx
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hRT : pResidual p G ⊔ (T : Subgroup G) ≤ centralizer ({a} : Set G) := by
    apply sup_le
    · intro r hr b hb
      obtain rfl := Set.mem_singleton_iff.mp hb
      exact mem_centralizer_iff.mp (hR hr) a ha
    · intro t ht b hb
      obtain rfl := Set.mem_singleton_iff.mp hb
      exact (congrArg Subtype.val (mem_center_iff.mp hxc ⟨t,ht⟩)).symm
  rw [pResidual_sup_sylow_eq_top T] at hRT
  refine ⟨a,ha,hane,mem_center_iff.mpr ?_⟩
  intro g
  exact ((hRT (mem_top g)) a rfl).symm
end Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]
/-- The nontrivial image of the prescribed subgroup meets the image-group center. -/
theorem exists_nontrivial_center_image_of_residual_centralizes
    {p : ℕ} [Fact p.Prime] (M A : Subgroup G) (hAM : A ≤ M)
    (hMn : M ≤ normalizer (A : Set G)) (hA : IsPGroup p A)
    (hR : (pResidual p M).map M.subtype ≤ centralizer (A : Set G))
    (f : G →* D) (hout : ¬ A ≤ f.ker) :
    ∃ a ∈ A.map f, a ≠ 1 ∧ a ∈ (center (M.map f)).map (M.map f).subtype := by
  let B := M.map f
  let : Finite B := Finite.of_surjective (f.subgroupMap M) (f.subgroupMap_surjective M)
  let C := (A.map f).subgroupOf B
  have hCB : A.map f ≤ B := map_mono hAM
  have hnorm : B ≤ normalizer (A.map f : Set D) :=
    (map_mono hMn).trans (A.le_normalizer_map f)
  let : C.Normal := (normal_subgroupOf_iff_le_normalizer hCB).mpr hnorm
  have hC : IsPGroup p C := (hA.map f).comap_subtype
  have hCne : C ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map B.subtype) he
    rw [map_subgroupOf_eq_of_le hCB, map_bot] at hh
    exact hout ((map_eq_bot_iff A).mp hh)
  have hR' : pResidual p B ≤ centralizer (C : Set B) := by
    intro r hr c hc
    apply Subtype.ext
    have hh : (r : D) ∈ ((pResidual p M).map M.subtype).map f := by
      rw [map_embedded_pResidual]
      exact mem_map_of_mem B.subtype hr
    have hz := (map_mono hR).trans (map_centralizer_le_centralizer_image (A : Set G) f) hh
    exact mem_centralizer_iff.mp hz c hc
  let T : Sylow p B := Classical.choice inferInstance
  obtain ⟨c,hc,hcne,hcc⟩ :=
    exists_nontrivial_center_mem_normal_of_residual_centralizes T C hC hCne hR'
  refine ⟨c,hc,?_,mem_map_of_mem B.subtype hcc⟩
  intro he
  exact hcne (Subtype.ext he)
end Subgroup
