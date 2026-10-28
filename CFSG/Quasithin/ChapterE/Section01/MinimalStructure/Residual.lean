module

public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Residuals of minimal supplements

If the two-residual of the quotient image is its solvable residual, the
same equality holds in the minimal supplement. Indeed, the solvable
residual times the prescribed Sylow subgroup covers the image, so
minimality makes this product the whole supplement. Its quotient by the
solvable residual is therefore a two-group; the reverse containment uses
solvability of two-group quotients.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
the last conclusion of E.1.10(4), printed p.211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem residual_sup_sylow (S : Sylow 2 G) :
    pResidual 2 G ⊔ (S : Subgroup G) = ⊤ := by
  let R := pResidual 2 G
  let q := QuotientGroup.mk' R
  have hS : (S : Subgroup G).map q = ⊤ :=
    ((S.mapSurjective (QuotientGroup.mk'_surjective R)).3
      ((isPGroup_quotient_pResidual 2).to_subgroup ⊤) le_top).symm
  have he := congrArg (Subgroup.comap q) hS
  rw [comap_map_eq, comap_top, QuotientGroup.ker_mk'] at he
  exact sup_comm R (S : Subgroup G) ▸ he

/-- The residual conclusion of E.1.10(4), using only its residual hypothesis. -/
theorem IsMinimalSupplement.pResidual_eq_solvableResidual (T : Sylow 2 G) {X Y K : Subgroup G} [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (hr : pResidual 2 (K.map (QuotientGroup.mk' Y)) =
      solvableResidual (K.map (QuotientGroup.mk' Y))) :
    pResidual 2 K = solvableResidual K := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let S : Sylow 2 K := T.subtype h.1.1
  have he : solvableResidual K ⊔ (S : Subgroup K) = ⊤ := by
    apply h.eq_top_of_map_eq_top _ le_sup_right
    rw [Subgroup.map_sup, map_solvableResidual_eq f hf, ← hr]
    exact residual_sup_sylow (S.mapSurjective hf)
  apply le_antisymm
  · exact sInf_le ⟨inferInstance,
      isPGroup_quotient_of_sup_eq_top _ _ S.isPGroup' he⟩
  · let : Group.IsNilpotent (K ⧸ pResidual 2 K) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _

end CFSG.Quasithin.ChapterE
