module
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.CentralKernelFixedComponents

/-!
# Normalizing a fixed component through its central quotient

Commuting actors permute ordinary components of the fixed group. If their nontrivial central-quotient images coincide, distinct components would make the same perfect image abelian. Thus quotient uniqueness normalizes the original component.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace MulAut
variable {E : Type*} [Group E]

/-- A unique fixed component downstairs fixes the containing component upstairs
under every actor commuting with the original involution. -/
theorem normalizes_fixed_component_of_central_quotient_unique
    (a b : MulAut E) (hab : Commute b a)
    (S : Subgroup E) (hS : IsComponentIn S a.fixedSubgroup)
    (hne : S.map (QuotientGroup.mk' (center E)) ≠ ⊥)
    (hunique : ∀ D₁ D₂ : Subgroup (E ⧸ center E),
      IsComponentIn D₁ (quotientAut (center E) a).fixedSubgroup →
      IsComponentIn D₂ (quotientAut (center E) a).fixedSubgroup → D₁ = D₂) :
    S.map b.toMonoidHom = S := by
  let q := QuotientGroup.mk' (center E)
  let aq := quotientAut (center E) a
  let bq := quotientAut (center E) b
  have hfix : a.fixedSubgroup.map b.toMonoidHom = a.fixedSubgroup := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxfix : a x = x := (mem_fixedSubgroup a x).mp hx
      apply (mem_fixedSubgroup a _).mpr
      have h := DFunLike.congr_fun hab.eq x
      change b (a x) = a (b x) at h
      rw [hxfix] at h
      exact h.symm
    · intro x hx
      refine ⟨b.symm x, ?_, b.apply_symm_apply x⟩
      have hxfix : a x = x := (mem_fixedSubgroup a x).mp hx
      apply (mem_fixedSubgroup a _).mpr
      apply b.injective
      have h := DFunLike.congr_fun hab.eq (b.symm x)
      change b (a (b.symm x)) = a (b (b.symm x)) at h
      rw [b.apply_symm_apply, hxfix] at h
      exact h.trans (b.apply_symm_apply x).symm
  let T := S.map b.toMonoidHom
  have hT : IsComponentIn T a.fixedSubgroup := hfix ▸ hS.map b
  have hcompat : ∀ x, q (a x) = aq (q x) :=
    fun x => (quotientAut_apply_mk (center E) a x).symm
  have hmap : T.map q = (S.map q).map bq.toMonoidHom := by
    rw [show T = S.map b.toMonoidHom from rfl, map_map, map_map]
    congr 1
    ext x
    exact (quotientAut_apply_mk (center E) b x).symm
  have hTne : T.map q ≠ ⊥ := by
    rw [hmap]
    exact fun h => hne (((S.map q).map_eq_bot_iff_of_injective bq.injective).mp h)
  have hSq := hS.map_fixed_of_central_ker a aq q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hcompat hne
  have hTq := hT.map_fixed_of_central_ker a aq q (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) hcompat hTne
  have he := hunique (S.map q) (T.map q) hSq hTq
  by_contra hTS
  have hcomm := hS.commutator_eq_bot_of_ne hT (fun h => hTS h.symm)
  have hm := congrArg (Subgroup.map q) hcomm
  rw [map_commutator, ← he, Subgroup.map_bot] at hm
  let : IsQuasisimple S := hS.quasisimple
  let : Group.IsPerfect (S.map q) :=
    Group.IsPerfect.ofSurjective (f := q.subgroupMap S) (q.subgroupMap_surjective S)
  rw [commutator_eq_self] at hm
  exact hne hm
end MulAut
