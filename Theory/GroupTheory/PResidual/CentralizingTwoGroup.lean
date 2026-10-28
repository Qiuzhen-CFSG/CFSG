module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Adjoining a commuting two-group preserves the two-residual

Split the second factor into its two-residual and a Sylow two-subgroup.
The latter joins the commuting two-group to form a normalizing two-group
supplement, which does not change the residual. All inclusions remain in
the original ambient group.

Source application: the two-factor centralizer in Aschbacher--Smith
15.1.16(a)--18, printed p.1092.
-/

public section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]
/-- A commuting two-group does not change the embedded two-residual. -/
theorem embedded_twoResidual_sup_of_centralizing_twoGroup
    (A B : Subgroup D) (hA : IsPGroup 2 A)
    (hc : A ≤ centralizer (B : Set D)) :
    (pResidual 2 (A ⊔ B : Subgroup D)).map (A ⊔ B).subtype =
      (pResidual 2 B).map B.subtype := by
  let E := (pResidual 2 B).map B.subtype
  let S : Sylow 2 B := Classical.choice inferInstance
  let C := (S : Subgroup B).map B.subtype
  have hEB : E ≤ B := map_subtype_le _
  have hCB : C ≤ B := map_subtype_le _
  have hBC : E ⊔ C = B := by
    have he := congrArg (Subgroup.map B.subtype) (pResidual_sup_sylow_eq_top S)
    simpa only [map_sup,←MonoidHom.range_eq_map,range_subtype] using he
  have hAC : A ≤ normalizer (C : Set D) :=
    (hc.trans (centralizer_le hCB)).trans (centralizer_le_normalizer _)
  have hp : IsPGroup 2 (A ⊔ C : Subgroup D) :=
    hA.to_sup_of_normal_right' (S.isPGroup'.map B.subtype) hAC
  have hn : A ⊔ C ≤ normalizer (E : Set D) := by
    apply sup_le
    · exact (hc.trans (centralizer_le hEB)).trans (centralizer_le_normalizer _)
    · exact hCB.trans (B.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image B (pResidual 2 B)))
  have he : A ⊔ B = E ⊔ (A ⊔ C) := by rw [←hBC]; ac_rfl
  rw [he]
  exact embedded_pResidual_join_pGroup E (A ⊔ C) (isPPerfect_embedded_pResidual 2 B) hp hn
end Subgroup
