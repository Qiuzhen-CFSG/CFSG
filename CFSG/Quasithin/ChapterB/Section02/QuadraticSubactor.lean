module
public import CFSG.Quasithin.ChapterB.Section02.QuadraticActors

/-!
# Quadratic replacement inside the original actor span

A maximum elementary subgroup moving a normal elementary module has a
quadratic maximum replacement inside its join with that module. The lift
retains its nontrivial action. Thus on every quotient action killing the
module, the replacement image is contained in the original actor image.

Source: Aschbacher–Smith B.1.4(3), B.2.8, and the Thompson image step in
3.1.9(5), printed pp.578.
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G]

theorem maxElementary_exists_quadratic_subactor (U S A : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hn : ¬ A ≤ centralizer (U : Set G)) :
    ∃ D ∈ elementaryAbelianMaxSubgroups S,
      ¬ D ≤ centralizer (U : Set G) ∧
      IsQuadratic (normalRepresentation U) D ∧ D ≤ A ⊔ U := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hne : A.map q ≠ ⊥ := by
    intro he
    exact hn (hk ▸ ((map_eq_bot_iff A).mp he))
  have hb := maxElementary_isBestOffender U q hq hk S A hUS hA hne
  obtain ⟨B,hB,hBA⟩ := hb.exists_minimal ρ
  let D := (A ⊓ B.comap q) ⊔ (U ⊓ centralizer (A ⊓ B.comap q : Set G))
  obtain ⟨hD,hDB⟩ := lemma_B_2_8_construct U q hq hk S hUS A hA B hB.1.1 hBA
  have hDn : ¬ D ≤ centralizer (U : Set G) := by
    intro hd
    have hc : D ≤ q.ker := hk.symm ▸ hd
    exact hB.1.1.1 (hDB.symm.trans ((map_eq_bot_iff D).mpr hc))
  refine ⟨D,hD,hDn,?_,sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)⟩
  have hquad := hB.isQuadratic ρ
  have he (g : G) (v : Additive U) : ρ (q g) v = normalRepresentation U g v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply U q hq hk g v
  intro a ha b hb v
  have hh := hquad (q a) (hDB ▸ mem_map_of_mem q ha)
    (q b) (hDB ▸ mem_map_of_mem q hb) v
  simpa only [he] using hh

end CFSG.Quasithin.ChapterB
