module
public import Theory.GroupTheory.PResidual.Restriction
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.IndexNormal

/-!
# Two-residuals of subgroups of index three

The action on three cosets makes the index of the normal core inside the
subgroup divide two. Its two-residual therefore equals the two-residual of
the normal core, and is normal in the ambient group. The relative version
keeps the original ambient embedding.

Source application: Aschbacher--Smith, 12.9.4, printed pp.859--860 of
refs/quasithin.pdf. It lifts normality of the original L₀ from the index-three
relation L₀T ≤ P inside the restricted component parabolic.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The embedded two-residual of an index-three subgroup is normal. -/
theorem normal_embedded_twoResidual_of_index_three (A : Subgroup G) (hi : A.index = 3) :
    ((pResidual 2 A).map A.subtype).Normal := by
  have hd : A.normalCore.index ∣ 6 := by
    have hh : A.normalCore.index ∣ A.index.factorial := by
      rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
      exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ A)).range
    simpa only [hi, Nat.factorial] using hh
  have hm := relIndex_mul_index A.normalCore_le
  rw [hi] at hm
  have hd2 : A.normalCore.relIndex A ∣ 2 := by
    apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 3)
    simpa only [hm] using hd
  let N := A.normalCore.subgroupOf A
  have hp : IsPGroup 2 (A ⧸ N) := by
    apply (isPGroup_iff_card_dvd_pow).mpr
    exact ⟨1,hd2⟩
  have hr : (pResidual 2 A).map A.subtype ≤ A.normalCore := by
    have hh : pResidual 2 A ≤ N := sInf_le ⟨inferInstance,hp⟩
    exact (map_mono hh).trans (map_subgroupOf_eq_of_le A.normalCore_le).le
  have he := embedded_pResidual_eq_of_le_of_residual_le 2 A.normalCore_le hr
  rw [←he]
  infer_instance

/-- The containing subgroup normalizes the original embedded two-residual. -/
theorem normalizes_embedded_twoResidual_of_relIndex_three
    {A P : Subgroup G} (hAP : A ≤ P) (hi : A.relIndex P = 3) :
    P ≤ normalizer ((pResidual 2 A).map A.subtype : Set G) := by
  let R := (pResidual 2 (A.subgroupOf P)).map (A.subgroupOf P).subtype
  let : R.Normal := normal_embedded_twoResidual_of_index_three (A.subgroupOf P) hi
  have hh := R.le_normalizer_map P.subtype
  rw [R.normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have he : R.map P.subtype = (pResidual 2 A).map A.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hAP]
  rwa [he] at hh
end Subgroup
