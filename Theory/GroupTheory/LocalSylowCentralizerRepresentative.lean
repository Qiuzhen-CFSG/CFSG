module
public import Theory.GroupTheory.SaturatedCentralizer

/-!
# Selecting a local Sylow centralizer

An element of an ambient Sylow subgroup T contained in M has an M-conjugate
whose T-centralizer is Sylow in its M-centralizer. Apply saturated-centralizer
selection inside M and transport its maximality through the literal subtype
map. The conjugating element belongs to M, allowing M-invariant families to
retain their membership and ambient centralizer bounds to transport back.

Source: Aschbacher--Smith, original 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Select an M-conjugate with the literal local Sylow-centralizer equation. -/
theorem exists_conjugate_local_centralizer_sylow
    (T : Sylow p G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (u : G) (hu : u ∈ (T : Subgroup G)) :
    ∃ g ∈ M, ∃ S : Sylow p (M ⊓ centralizer ({g * u * g⁻¹} : Set G) : Subgroup G),
      (S : Subgroup _).map (M ⊓ centralizer ({g * u * g⁻¹} : Set G)).subtype =
        (T : Subgroup G) ⊓ centralizer ({g * u * g⁻¹} : Set G) := by
  let R := T.subtype hTM
  let x : R := ⟨⟨u,hTM hu⟩,hu⟩
  obtain ⟨v,hxv,hmax⟩ := R.exists_conjugate_with_saturated_centralizer x
  obtain ⟨g,hg⟩ := isConj_iff.mp hxv
  let w : G := v
  have hw : (g : G) * u * (g : G)⁻¹ = w := congrArg Subtype.val hg
  refine ⟨g,g.property,?_⟩
  rw [hw]
  let A := (centralizer ({v} : Set R)).map (R : Subgroup M).subtype
  let B := (T : Subgroup G) ⊓ centralizer ({w} : Set G)
  let C := M ⊓ centralizer ({w} : Set G)
  have hAB : A.map M.subtype = B := by
    dsimp only [A]
    rw [map_subtype_centralizer_singleton]
    ext y
    constructor
    · rintro ⟨y,⟨hyR,hyC⟩,rfl⟩
      exact ⟨hyR,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hyC))⟩
    · intro hy
      exact ⟨⟨y,hTM hy.1⟩,⟨hy.1,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hy.2))⟩,rfl⟩
  have hBC : B ≤ C := le_inf (inf_le_left.trans hTM) inf_le_right
  have hp : IsPGroup p B := T.isPGroup'.of_injective
    (inclusion (inf_le_left : B ≤ (T : Subgroup G))) (inclusion_injective _)
  obtain ⟨S,hS⟩ := (hp.comap_subtype (K := C)).exists_le_sylow
  refine ⟨S,?_⟩
  let V := (S : Subgroup C).map C.subtype
  have hVM : V ≤ M := (map_subtype_le _).trans inf_le_left
  have hBV : B ≤ V := by
    rw [← map_subgroupOf_eq_of_le hBC]
    exact map_mono hS
  have he : V.subgroupOf M = A := hmax _ (S.isPGroup'.map C.subtype).comap_subtype
    (by
      intro y hy
      apply hBV
      rw [← hAB]
      exact mem_map_of_mem M.subtype hy)
    (by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp ((map_subtype_le _ hy).2))))
  have he' := congrArg (map M.subtype) he
  rwa [map_subgroupOf_eq_of_le hVM,hAB] at he'

end Sylow
