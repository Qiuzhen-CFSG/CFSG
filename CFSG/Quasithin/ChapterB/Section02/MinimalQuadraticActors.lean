module
public import CFSG.Quasithin.ChapterB.Section02.QuadraticActors

/-!
# Quadratic replacement with minimal image modulo a normal subgroup

Choose a maximum elementary subgroup with the smallest nontrivial image
modulo N, then perform Thompson replacement on its faithful action on U.
The replacement remains inside AU, so U ≤ N preserves minimality of its
image modulo N. The action kernel and the hypothesis on maximum subgroups
inside N ensure that the replacement still escapes N.

Source: Aschbacher--Smith D.1.3(2), using B.1.4(3) and B.2.8;
this is the actor selection used in 15.1.12(4), printed p.1090.
-/

public section
namespace CFSG.Quasithin.ChapterB
open Subgroup Stellmacher Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection
variable {G : Type*} [Group G] [Finite G]

theorem maxElementary_exists_quadratic_minimal_outside (U S N : Subgroup G)
    [U.Normal] [N.Normal] [IsElementaryAbelian 2 U] (hUS : U ≤ S) (hUN : U ≤ N)
    (hkernel : S ⊓ centralizer (U : Set G) ≤ N)
    (hinside : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      A ≤ N → A ≤ centralizer (U : Set G))
    (hex : ∃ A ∈ elementaryAbelianMaxSubgroups S, ¬ A ≤ N) :
    ∃ A ∈ elementaryAbelianMaxSubgroups S, ¬ A ≤ N ∧
      IsQuadratic (normalRepresentation U) A ∧
      ∀ B ∈ elementaryAbelianMaxSubgroups S, ¬ B ≤ N → N.relIndex A ≤ N.relIndex B := by
  classical
  have hexn : ∃ n : ℕ, ∃ A ∈ elementaryAbelianMaxSubgroups S,
      ¬ A ≤ N ∧ N.relIndex A = n := by
    obtain ⟨A,hA,hAN⟩ := hex
    exact ⟨_,A,hA,hAN,rfl⟩
  obtain ⟨A,hA,hAN,hmin⟩ := Nat.find_spec hexn
  have hminimal : ∀ B ∈ elementaryAbelianMaxSubgroups S,
      ¬ B ≤ N → N.relIndex A ≤ N.relIndex B := by
    intro B hB hBN
    rw [hmin]
    exact Nat.find_min' hexn ⟨B,hB,hBN,rfl⟩
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let ρ := NormalElementaryQuotient.representation U q hq hk
  have hn : ¬ A ≤ centralizer (U : Set G) :=
    fun hn => hAN ((le_inf hA.1 hn).trans hkernel)
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
  have hDA : N.relIndex D ≤ N.relIndex A := by
    have hd : D ≤ A ⊔ N := sup_le (inf_le_left.trans le_sup_left)
      ((inf_le_left.trans hUN).trans le_sup_right)
    simpa only [relIndex_sup_right] using
      relIndex_le_of_le_right (H := N) hd index_ne_zero_of_finite
  refine ⟨D,hD,hDn,?_,fun E hE hEN => hDA.trans (hminimal E hE hEN)⟩
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
