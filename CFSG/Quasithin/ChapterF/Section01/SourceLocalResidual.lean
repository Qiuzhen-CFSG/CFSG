module
public import CFSG.Quasithin.ChapterF.Section01.SourceStarredParabolic
public import Theory.GroupTheory.SolvableResidual.CoreOrder

/-!
# The original source factors and their parabolic residuals

For the genuine F.1.1 pair, P_i=L_i B with L_i normal and B solvable.
Thus P_i/L_i is solvable. The original L_i and P_i have the same embedded
solvable residual. Solvability of P_i is likewise equivalent to solvability
of the literal quotient L_i/O_2(L_i).

The A5 application identifies the original L_i with the parabolic residual
from its actual core containment; perfectness of A5 removes the need for
a separate residual-order premise. Core containment is an explicit model
input after recognition; no weak-BN classification or
arbitrary replacement of L_i is asserted here.

Source: Aschbacher--Smith F.1.3 and F.1.12, printed pp.260 and 263--264.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
private theorem parabolic_quotient_solvable (h : HypothesisF11 L S) (i : Fin 2) :
    letI := h.local_normal_in_parabolic i
    Group.IsSolvable ((parabolic L S i) ⧸ ((L i).subgroupOf (parabolic L S i))) := by
  let := h.local_normal_in_parabolic i
  let := h.commonBorel_solvable
  let P := parabolic L S i
  let N := (L i).subgroupOf P
  let D := (commonBorel L S).subgroupOf P
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (commonBorel_le_parabolic (L := L) (S := S) i)).toMonoidHom)
    (subgroupOfEquivOfLe (commonBorel_le_parabolic (L := L) (S := S) i)).injective
  have hsup : N ⊔ D = ⊤ := by
    rw [← subgroupOf_sup (show L i ≤ P from le_sup_left.trans le_sup_left)
      (commonBorel_le_parabolic i), ← parabolic_eq_sup_commonBorel]
    exact subgroupOf_self P
  let q := QuotientGroup.mk' N
  let f : D →* P ⧸ N := q.comp D.subtype
  apply Group.isSolvable_of_surjective (f := f)
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  have hg : g ∈ N ⊔ D := by rw [hsup]; trivial
  obtain ⟨n, hn, d, hd, hgd⟩ :=
    (mem_sup_of_normal_left (s := N) (t := D)).mp hg
  have hqn : q n = 1 := (QuotientGroup.eq_one_iff (N := N) n).mpr hn
  refine ⟨⟨d, hd⟩, ?_⟩
  change q d = q g
  rw [← hgd, map_mul, hqn, one_mul]

theorem HypothesisF11.parabolic_residual_le_local (h : HypothesisF11 L S) (i : Fin 2) :
    (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype ≤ L i := by
  let := h.local_normal_in_parabolic i
  let := parabolic_quotient_solvable h i
  have hm := map_mono (f := (parabolic L S i).subtype)
    (solvableResidual_le_of_solvable_quotient ((L i).subgroupOf (parabolic L S i)))
  rwa [map_subgroupOf_eq_of_le (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left)] at hm

theorem HypothesisF11.local_residual_eq_parabolic (h : HypothesisF11 L S) (i : Fin 2) :
    (solvableResidual (L i)).map (L i).subtype =
      (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype := by
  let := h.finite_parabolic i
  let := h.finite_local i
  let R := (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (parabolic L S i).subtype.subgroupMap (solvableResidual (parabolic L S i)))
    (MonoidHom.subgroupMap_surjective _ _)
  exact le_antisymm (map_solvableResidual_mono (le_sup_left.trans le_sup_left))
    (le_map_solvableResidual_of_isPerfect R (L i) (h.parabolic_residual_le_local i))

/-- The original A5 factor is the parabolic residual once the model core lies in it. -/
theorem HypothesisF11.a5_local_eq_parabolic_residual_of_core_le (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hcore : pCore 2 (parabolic L S i) ≤ solvableResidual (parabolic L S i)) :
    L i = (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype := by
  let := h.finite_parabolic i
  let N := (L i).subgroupOf (parabolic L S i)
  let := h.local_normal_in_parabolic i
  let d : N ≃* L i := subgroupOfEquivOfLe (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left)
  let de := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (N ⧸ pCore 2 N) :=
    Group.IsPerfect.ofSurjective (f := de.symm.toMonoidHom) de.symm.surjective
  let := parabolic_quotient_solvable h i
  have hn := normal_eq_solvableResidual_of_perfect_core_quotient 2 N hcore
  have hm := congrArg (map (parabolic L S i).subtype) hn
  rwa [map_subgroupOf_eq_of_le (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left)] at hm

theorem HypothesisF11.a5_local_eq_parabolic_residual (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (hcore : pCore 2 (parabolic L S i) ≤ solvableResidual (parabolic L S i))
    (hcard : Nat.card (solvableResidual (parabolic L S i)) =
      60 * Nat.card (pCore 2 (parabolic L S i))) :
    L i = (solvableResidual (parabolic L S i)).map (parabolic L S i).subtype := by
  let := h.finite_parabolic i
  let := h.local_normal_in_parabolic i
  let := parabolic_quotient_solvable h i
  let N := (L i).subgroupOf (parabolic L S i)
  let d : N ≃* L i := subgroupOfEquivOfLe (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left)
  let de := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  have hc : Nat.card (N ⧸ pCore 2 N) = 60 := by
    rw [Nat.card_congr (de.trans e).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hn := normal_eq_solvableResidual_of_core_order 2 N hcore (by rw [hc]; exact hcard)
  have hm := congrArg (map (parabolic L S i).subtype) hn
  rwa [map_subgroupOf_eq_of_le (show L i ≤ parabolic L S i from
    le_sup_left.trans le_sup_left)] at hm
end CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.ChapterF.Source
open Subgroup
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
theorem HypothesisF11.parabolic_solvable_iff_local_quotient
    (h : HypothesisF11 L S) (i : Fin 2) :
    Group.IsSolvable (parabolic L S i) ↔ Group.IsSolvable (L i ⧸ pCore 2 (L i)) := by
  constructor
  · intro hp
    let := hp
    let : Group.IsSolvable (L i) := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show L i ≤ parabolic L S i from le_sup_left.trans le_sup_left))
      (inclusion_injective _)
    infer_instance
  · intro hq
    let := h.finite_local i
    let := hq
    let : Group.IsNilpotent (pCore 2 (L i)) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable (L i) :=
      (Group.isSolvable_iff_subgroup_quotient (pCore 2 (L i))).mpr
        ⟨inferInstance, inferInstance⟩
    let := h.commonBorel_solvable
    rw [parabolic_eq_sup_commonBorel]
    exact Group.isSolvable_sup_of_normalizes _ _ (h.commonBorel_normalizes_local i)
end CFSG.Quasithin.ChapterF.Source
