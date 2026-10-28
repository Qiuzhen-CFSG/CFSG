module
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.GroupAction.NormalPChiefSeries.Linear

/-!
# Quadratic maximal elementary actors outside a subgroup

A moving maximum elementary subgroup gives a best offender on the faithful
centralizer quotient. Thompson replacement selects an equal-weight quadratic
offender, and B.2.8 lifts it to another maximum elementary subgroup. If every
maximum member inside N centralizes U, the nontrivial replacement image
forces the lifted subgroup outside N. The conclusion uses the literal
conjugation representation on U.

Source application: Aschbacher–Smith, D.1.3(2), printed p.173, with the
replacement and lift supplied by B.1.4(3) and B.2.8.
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G]

theorem maxElementary_exists_quadratic_outside (U S N : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S)
    (hinside : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      A ≤ N → A ≤ centralizer (U : Set G))
    (hex : ∃ A ∈ elementaryAbelianMaxSubgroups S, ¬ A ≤ centralizer (U : Set G)) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ¬ A ≤ N ∧
      IsQuadratic (normalRepresentation U) A := by
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨A,hA,hn⟩ := hex
  have hne : A.map q ≠ ⊥ := by
    intro he
    exact hn (hk ▸ ((map_eq_bot_iff A).mp he))
  have hb := maxElementary_isBestOffender U q hq hk S A hUS hA hne
  obtain ⟨B,hB,hBA⟩ := hb.exists_minimal ρ
  let D := (A ⊓ B.comap q) ⊔ (U ⊓ centralizer (A ⊓ B.comap q : Set G))
  obtain ⟨hD,hDB⟩ := lemma_B_2_8_construct U q hq hk S hUS A hA B hB.1.1 hBA
  have hDn : ¬ D ≤ N := by
    intro hd
    have hc : D ≤ q.ker := hk.symm ▸ hinside D hD hd
    exact hB.1.1.1 (hDB.symm.trans ((map_eq_bot_iff D).mpr hc))
  refine ⟨D,hD,hDn,?_⟩
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
