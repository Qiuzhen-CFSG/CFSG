module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Theory.ElementaryAbelian.Injective

/-!
# Centralizing actors in a normalizer action

An ambient subgroup which normalizes K and centralizes A maps into the pointwise
fixer of the literal subgroup A intersect K inside Aut(K). Faithfulness of the
normalizer action makes this restricted map injective. Source applications are
the original supplements and centralizers in Aschbacher–Smith 14.3.19–20.
-/

@[expose] public section
namespace Subgroup
variable {G:Type*} [Group G]

/-- Restrict the literal normalizer action to actors centralizing an ambient subgroup. -/
noncomputable def normalizerFixerHom (K A D:Subgroup G)
    (hn:D≤normalizer (K:Set G)) (hc:D≤centralizer (A:Set G)) :
    D→*fixingSubgroup (MulAut K) (A.subgroupOf K:Set K) :=
  (K.normalizerMonoidHom.comp (inclusion hn)).codRestrict _ (by
    intro d
    rw [mem_fixingSubgroup_iff]
    intro a ha
    apply Subtype.ext
    change (d:G)*(a:G)*(d:G)⁻¹=(a:G)
    have hh : (a:G)*(d:G)=(d:G)*(a:G) := hc d.property (a:G) ha
    rw [←hh,mul_assoc,mul_inv_cancel,mul_one])

theorem normalizerFixerHom_injective (K A D:Subgroup G)
    (hn:D≤normalizer (K:Set G)) (hc:D≤centralizer (A:Set G))
    (hf:Function.Injective K.normalizerMonoidHom) :
    Function.Injective (normalizerFixerHom K A D hn hc) := by
  intro x y h
  apply inclusion_injective hn
  apply hf
  exact congrArg Subtype.val h

end Subgroup
