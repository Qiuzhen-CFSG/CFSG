module
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerConjugacy.FullStructure
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Common Sylow nine-groups from an external cubic

A faithful three-group of automorphisms of UT₃(F₄) embeds in the diagonal
Sylow E₉, so it is elementary and its order divides nine. If an ambient
normal subgroup has three-divisible order and a prescribed cubic lies
outside it, any Sylow containing that cubic must have order nine: a cubic
Sylow would be contained in the normal subgroup by Sylow intersection.

The action may have a three-prime kernel; its restriction to the selected
Sylow is automatically faithful. This constructs the E₉ required after the
exceptional reduction in Aschbacher--Smith 2.5.7, printed p.556.
-/
public section

open Subgroup
open scoped IsMulCommutative
namespace Matrix.PSL3Four.RootNormalizerModel
open AutomizerConjugacy

private theorem unitsPair_elementary : IsElementaryAbelian 3 (Fˣ × Fˣ) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro a
    have h (u : Fˣ) : u ^ 3 = 1 := by
      have hc : Nat.card Fˣ = 3 := by rw [Nat.card_units, card_F]
      simpa only [hc] using (pow_card_eq_one' : u ^ Nat.card Fˣ = 1)
    exact Prod.ext (h a.1) (h a.2)

theorem faithful_three_action
    {Y : Type*} [Group Y] [Finite Y] (hY : IsPGroup 3 Y)
    (f : Y →* MulAut Root) (hf : Function.Injective f) :
    Nat.card Y ∣ 9 ∧ IsElementaryAbelian 3 Y := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨T, hT⟩ := torus_sylow
  obtain ⟨S, hS⟩ := (hY.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  have hc : Nat.card (S : Subgroup (MulAut Root)) = 9 := by
    calc _ = Nat.card (T : Subgroup (MulAut Root)) := Nat.card_congr (S.equiv T).toEquiv
         _ = 9 := by rw [hT, torus_card]
  let eS : S ≃* Fˣ × Fˣ := ((S.equiv T).trans (MulEquiv.subgroupCongr hT)).trans
    (MonoidHom.ofInjective Cubic.diagonalHom_injective).symm
  let : IsElementaryAbelian 3 (Fˣ × Fˣ) := unitsPair_elementary
  let : IsElementaryAbelian 3 S := IsElementaryAbelian.of_injective eS.toMonoidHom eS.injective
  let g : Y →* S := f.codRestrict S (fun y => hS ⟨y, rfl⟩)
  have hg : Function.Injective g := by
    intro a b h
    exact hf (congrArg Subtype.val h)
  refine ⟨?_, IsElementaryAbelian.of_injective g hg⟩
  have hh := card_dvd_of_injective g hg
  rwa [hc] at hh

end Matrix.PSL3Four.RootNormalizerModel

namespace Subgroup
open Matrix.PSL3Four.RootNormalizerModel
variable {G : Type*} [Group G] [Finite G]

theorem exists_nine_sylow_above_external_cubic
    (f : G →* MulAut Root) (hk : Nat.Coprime 3 (Nat.card f.ker))
    (J X : Subgroup G) [J.Normal] (hJ : 3 ∣ Nat.card J)
    (hX : Nat.card X = 3) (hXJ : ¬ X ≤ J) :
    ∃ P : Sylow 3 G, X ≤ P ∧ Nat.card (P : Subgroup G) = 9 ∧
      IsElementaryAbelian 3 P := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨P, hXP⟩ := (IsPGroup.of_card (p := 3) (n := 1) hX).exists_le_sylow
  have hi := injective_comp_subtype_of_coprime_ker f hk P P.isPGroup'
  obtain ⟨hdiv, he⟩ := faithful_three_action P.isPGroup' (f.comp (P : Subgroup G).subtype) hi
  have hcases : Nat.card P = 1 ∨ Nat.card P = 3 ∨ Nat.card P = 9 := by
    obtain ⟨k, hk, heq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
      (show Nat.card P ∣ 3 ^ 2 from hdiv)
    interval_cases k
    · exact Or.inl heq
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr heq)
  have hlow := card_le_of_le hXP
  rw [hX] at hlow
  have h9 : Nat.card P = 9 := by
    rcases hcases with h1 | h3 | h9
    · omega
    · obtain ⟨Q, hQ⟩ := P.exists_subgroupOf_eq_of_normal J
      have hQ3 : 3 ∣ Nat.card Q := by
        have hh : 3 ∣ Nat.card Q * (Q : Subgroup J).index := by
          rw [(Q : Subgroup J).card_mul_index]
          exact hJ
        exact (Nat.prime_three.dvd_mul.mp hh).resolve_right Q.not_dvd_index
      have hmap : (Q : Subgroup J).map J.subtype ≤ (P : Subgroup G) := by
        rw [hQ, subgroupOf_map_subtype]
        exact inf_le_left
      have heq : (Q : Subgroup J).map J.subtype = (P : Subgroup G) := by
        apply eq_of_le_of_card_ge hmap
        rw [card_map_of_injective J.subtype_injective, h3]
        exact Nat.le_of_dvd Nat.card_pos hQ3
      exact (hXJ (hXP.trans (heq.symm.le.trans (map_subtype_le _)))).elim
    · exact h9
  exact ⟨P, hXP, h9, he⟩
end Subgroup
