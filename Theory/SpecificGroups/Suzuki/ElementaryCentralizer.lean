module
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.PrimeRankHom
public import Theory.GroupTheory.PrimeRankZero
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary nine-subgroups acting on a normal Suzuki group

The inner automorphism group has order prime to three, while the actual
outer automorphism group is cyclic. The kernel/image rank bound gives
three-rank at most one for the full automorphism group. Hence an elementary
nine-subgroup acting on a normal Suzuki subgroup has a nontrivial actual
centralizer intersection. No splitting of the automorphism group is used.

Source: Aschbacher--Smith 12.6.31, printed p.836; the Suzuki outer-group
input is GLS3, Theorem 2.5.12, refs/KGroup/GLS3/chapter2.tex.
-/

public section
open Subgroup Theory.GroupTheory
namespace BenderSuzuki.MatrixGroups

/-- Cyclic outer automorphisms and the three-free inner group bound the
three-rank of the full Suzuki automorphism group by one. -/
theorem suzuki_automorphism_threeRank_le_one (m : ℕ) (hm : 0 < m) :
    primeRank 3 (MulAut (SuzukiMatrixGroup m)) ≤ 1 := by
  let X := SuzukiMatrixGroup m
  let : IsCyclic (MulAut.Outer X) := suzuki_outer_isCyclic m (by omega)
  have hi : primeRank 3 (MulAut.innerSubgroup X) = 0 :=
    PrimeRank.eq_zero_iff_not_dvd_card.mpr (fun hd =>
      suzukiMatrixGroup_three_free m hm (hd.trans (card_range_dvd MulAut.conj)))
  let P : Sylow 3 (MulAut.Outer X) := Classical.choice inferInstance
  have ho : primeRank 3 (MulAut.Outer X) ≤ 1 :=
    P.primeRank_le_one_of_isCyclic inferInstance
  have hr := primeRank_le_ker_add (p := 3)
    (QuotientGroup.mk' (MulAut.innerSubgroup X))
  rw [QuotientGroup.ker_mk',hi,zero_add] at hr
  exact hr.trans ho

/-- An E₉ in an overgroup of a normal Suzuki subgroup has nontrivial
intersection with that subgroup's centralizer. Normality is in the overgroup. -/
theorem elementary_nine_centralizer_normal_suzuki_ne_bot
    {G : Type*} [Group G] [Finite G] (K A : Subgroup G) [K.Normal]
    [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    {m : ℕ} (hm : 0 < m) (e : K ≃* SuzukiMatrixGroup m) :
    A ⊓ centralizer (K : Set G) ≠ ⊥ := by
  intro hz
  let f : A →* MulAut K := (MulAut.conjNormal : G →* MulAut K).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply f.ker.eq_bot_iff_forall.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hz]
    refine ⟨x.property,?_⟩
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact hx
  let : IsElementaryAbelian 3 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup A).subtype (⊤ : Subgroup A).subtype_injective
  have hl : 2 ≤ primeRank 3 A :=
    IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup A) (by
      rw [Nat.card_congr Subgroup.topEquiv.toEquiv,hA]; norm_num)
  have hr := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have he := primeRank_equiv 3 (MulAut.congr e)
  have hu := suzuki_automorphism_threeRank_le_one m hm
  omega
end BenderSuzuki.MatrixGroups
