module
public import Theory.GroupTheory.ElementaryThompsonComponent

/-!
# Relative elementary Thompson subgroups

Normalizer invariance needs no finiteness. Thompson heredity between J(R)
and R, and nontriviality for a nontrivial two-group R, need only that R
itself is finite. Transport through R's subtype map preserves the literal
ambient subgroup and avoids imposing finiteness on an amalgam's ambient
carrier. Source application: Aschbacher–Smith, D.1.4, printed p.176.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G]
theorem normalizer_le_normalizer_elementaryAbelianMaxJ (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change R.map (MulAut.conj g).toMonoidHom = R at hg
  change (elementaryAbelianMaxJ R).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv,hg]

theorem elementaryAbelianMaxJ_eq_of_intermediate_finite
    (R B : Subgroup G) [Finite R] (hJB : elementaryAbelianMaxJ R ≤ B) (hBR : B ≤ R) :
    elementaryAbelianMaxJ B = elementaryAbelianMaxJ R := by
  have htop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map,range_subtype]
  have hJ : (elementaryAbelianMaxJ (⊤ : Subgroup R)).map R.subtype = elementaryAbelianMaxJ R := by
    rw [← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,htop]
  have hJB' : elementaryAbelianMaxJ (⊤ : Subgroup R) ≤ B.subgroupOf R := by
    intro x hx
    exact hJB (hJ ▸ mem_map_of_mem R.subtype hx)
  have he := elementaryAbelianMaxJ_eq_of_intermediate (⊤ : Subgroup R) (B.subgroupOf R) hJB' le_top
  have hm := congrArg (map R.subtype) he
  rw [← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
    ← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
    map_subgroupOf_eq_of_le hBR,htop] at hm
  exact hm

theorem elementaryAbelianMaxJ_ne_bot_of_finite_pGroup
    (R : Subgroup G) [Finite R] (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    elementaryAbelianMaxJ R ≠ ⊥ := by
  let : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have hj := elementaryAbelianMaxJ_top_ne_bot_of_isPGroup hp
  intro hz
  apply hj
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply Subtype.ext
  have hm : (x : G) ∈ elementaryAbelianMaxJ R := by
    have hh := mem_map_of_mem R.subtype hx
    rw [← elementaryAbelianMaxJ_map_injective R.subtype R.subtype_injective,
      ← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  exact mem_bot.mp (hz ▸ hm)
end Stellmacher

