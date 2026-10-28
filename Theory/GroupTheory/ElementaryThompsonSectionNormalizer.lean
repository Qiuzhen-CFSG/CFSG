module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Thompson normality from a normalized section centralizer

Suppose J(T) centralizes P and normalizes Y, where Y normalizes P and
C_Y(P) is a two-group. If a Sylow two-subgroup of Y lies in T, then Y
normalizes J(T). Indeed, adjoin J(T) to Y. The enlarged group has its
Sylow subgroup inside T, and its P-centralizer is the two-group
C_Y(P)J(T). Thompson heredity identifies the Thompson subgroup of this
normal centralizer with J(T).

This keeps the original centralizer and avoids choosing a new section.
Source application: Aschbacher–Smith, proof of 14.7.32, printed p.1058.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- A normalizing, centralizing Thompson subgroup is normalized by the original actor. -/
theorem normalizes_maxJ_of_normalizing_centralized_section (T : Sylow 2 G) (Y P : Subgroup G)
    (hYP : Y ≤ normalizer (P : Set G))
    (hker : IsPGroup 2 (Y ⊓ centralizer (P : Set G) : Subgroup G))
    (hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (P : Set G))
    (hJY : elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (Y : Set G))
    (S : Sylow 2 Y) (hST : (S : Subgroup Y).map Y.subtype ≤ (T : Subgroup G)) :
    Y ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let C := centralizer (P : Set G)
  let R := (S : Subgroup Y).map Y.subtype ⊔ J
  let D := Y ⊔ J
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hRT : R ≤ (T : Subgroup G) := sup_le hST hJT
  have hRY : R ≤ normalizer (Y : Set G) :=
    sup_le ((map_subtype_le _).trans Y.le_normalizer) hJY
  obtain ⟨S',hS'⟩ := IsPGroup.exists_sylow_sup_of_coprime_index Y R
    (T.isPGroup'.to_le hRT) hRY (S : Subgroup Y) S.not_dvd_index le_sup_left
  have hD : Y ⊔ R = D := by
    apply le_antisymm
    · exact sup_le le_sup_left (sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right)
    · exact sup_le le_sup_left (le_sup_right.trans le_sup_right)
  let C' := D ⊓ C
  have hDC : D ≤ normalizer (C : Set G) :=
    sup_le (hYP.trans (normalizer_le_normalizer_centralizer P)) (hJC.trans C.le_normalizer)
  have hnorm : D ≤ normalizer (C' : Set G) :=
    (le_inf D.le_normalizer hDC).trans inf_normalizer_le_normalizer_inf
  have hEq : C' = (Y ⊓ C) ⊔ J := by
    apply le_antisymm
    · intro x hx
      have hxD : x ∈ (Y : Set G) * (J : Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left Y J hJY]
        exact hx.1
      obtain ⟨y,hy,j,hj,rfl⟩ := hxD
      have hyC : y ∈ C := by
        have hh := C.mul_mem hx.2 (C.inv_mem (hJC hj))
        simpa only [mul_inv_cancel_right] using hh
      exact ((Y ⊓ C) ⊔ J).mul_mem (mem_sup_left ⟨hy,hyC⟩) (mem_sup_right hj)
    · exact sup_le (inf_le_inf_right C le_sup_left) (le_inf le_sup_right hJC)
  have hp : IsPGroup 2 C' := by
    rw [hEq]
    exact hker.to_sup_of_normal_left' (T.isPGroup'.to_le hJT)
      ((le_inf hJY (hJC.trans C.le_normalizer)).trans inf_normalizer_le_normalizer_inf)
  have hCT : C' ≤ (T : Subgroup G) := by
    have hcore : C' ≤ (Y ⊔ R : Subgroup G).pCoreIn 2 :=
      le_pCoreIn_of_normalizes hp (inf_le_left.trans hD.ge) (hD ▸ hnorm)
    exact hcore.trans ((pCoreIn_le_sylow _ S').trans (hS'.le.trans hRT))
  have hJC' : J ≤ C' := le_inf le_sup_right hJC
  have he : elementaryAbelianMaxJ C' = J :=
    elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) C' hJC' hCT
  have hh := hnorm.trans (normalizer_le_normalizer_elementaryAbelianMaxJ C')
  rw [he] at hh
  exact le_sup_left.trans hh
end Subgroup
