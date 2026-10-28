module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.Models
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LinearModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Reduction
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# Actors and ambient tau in the linear prime-square models

An actual PSL₂ or PGL₂ realization over an odd field of order greater than
three has trivial two-core. For PGL₂ this follows from the faithful normal
simple PSL₂ layer. The linear embedding bounds the elementary two-rank by
two, so a large actor is a four-group. Its self-centralizer and the trivial
two-core identify ambient tau with the actor itself.

`LinearWitnesses.isEMemberAt_of_localModel` uses these facts to discharge
E.1.2(E0) for the concrete S₄ and dihedral local subgroups. No placement or
escape is asserted here. The bounds include field orders nine and twenty-five.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--2 and E.1.14(6), printed pp.209--210 and 214. The model facts come
from the actual projective-linear groups in the Gorenstein--Walter library.
-/

public section

open Subgroup GorensteinWalter Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses

variable {F : Type*} [Field F] [Finite F]
variable {G : Type*} [Group G] [Finite G]

private theorem psl_twoCore_eq_bot (hlarge : 3 < Nat.card F) :
    pCore 2 (PSL2 F) = ⊥ := by
  let : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F hlarge
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 2 (PSL2 F)) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (⊤ : Subgroup (PSL2 F)) := h ▸ pCore_isPGroup
    have hp' : IsPGroup 2 (PSL2 F) := hp.of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent (PSL2 F) := hp'.isNilpotent
    exact (Group.IsPerfect.not_isSolvable (PSL2 F) inferInstance).elim

private theorem pgl_twoCore_eq_bot (hodd : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F) : pCore 2 (PGL2 F) = ⊥ := by
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : IsSimpleGroup (PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F hlarge
  let L : Subgroup (PGL2 F) := Matrix.ProjectiveSpecialLinearGroup.toPGL.range
  let e : PSL2 F ≃* L := psl2EquivToPGLRange F
  let : L.Normal := normal_of_index_eq_two (pgl2_psl2Range_index_eq_two F hodd)
  let : IsSimpleGroup L := e.symm.isSimpleGroup
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact SimpleSocle.pCore_eq_bot
    (SimpleSocle.radical_eq_bot L (pgl2_psl2Range_centralizer_eq_bot F hodd)) 2

omit [Finite G] in
/-- The actual linear alternatives have no normal two-subgroup. -/
theorem twoCore_eq_bot (hodd : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F)
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F)) :
    pCore 2 G = ⊥ := by
  rcases hmodel with he | he
  all_goals obtain ⟨e⟩ := he
  · rw [← pCore_map_iso 2 e.symm, psl_twoCore_eq_bot hlarge, Subgroup.map_bot]
  · rw [← pCore_map_iso 2 e.symm, pgl_twoCore_eq_bot hodd hlarge, Subgroup.map_bot]

omit [Finite F] [Finite G] in
/-- Retain a genuine linear embedding for both model alternatives. -/
theorem exists_linear_embedding
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F)) :
    ∃ j : G →* PGL2 F, Function.Injective j := by
  rcases hmodel with he | he
  all_goals obtain ⟨e⟩ := he
  · exact ⟨Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom,
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective⟩
  · exact ⟨e.toMonoidHom, e.injective⟩

/-- The large actors in a linear model are four-groups, not rank-three actors. -/
theorem large_actor_isKleinFour (hodd : IsOddPrimePower (Nat.card F))
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F))
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hr : 1 < Group.rank A) :
    IsKleinFour A := by
  let : Finite (PGL2 F) := Finite.of_surjective
    Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨j, hj⟩ := exists_linear_embedding hmodel
  have hbound : primeRank 2 G ≤ 2 :=
    (primeRank_le_of_injective 2 j hj).trans (Theory.PSL2.odd_pgl_two_rank F hodd)
  have hc : Nat.card A ≤ 4 :=
    (primeRank_le_iff_elementary_card_le G).mp hbound A inferInstance
  have hc2 : 2 < Nat.card A := by
    by_contra h
    have hrle := IsElementaryAbelian.rank_le_of_card_le (p := 2) (n := 1) A
      (show Nat.card A ≤ 2 ^ 1 by simpa using Nat.le_of_not_gt h)
    omega
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn2 : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (show 2 ^ n ≤ 2 ^ 2 by omega)
  have hc4 : Nat.card A = 4 := by
    interval_cases n <;> norm_num only [Nat.reducePow] at hn <;> omega
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hc4, IsElementaryAbelian.exponent_eq_prime⟩

omit [Finite G] in
/-- Every four-group in either actual linear model is self-centralizing. -/
theorem kleinFour_centralizer_eq_self (hodd : IsOddPrimePower (Nat.card F))
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F))
    (A : Subgroup G) (hA : IsKleinFour A) : centralizer (A : Set G) = A := by
  obtain ⟨j, hj⟩ := exists_linear_embedding hmodel
  exact PrimeGeometry.kleinFour_selfCentralizing_of_embedding hodd j hj A hA

/-- The ambient tau condition is exactly actor containment in either linear model. -/
theorem tau_eq_actor (hodd : IsOddPrimePower (Nat.card F))
    (hlarge : 3 < Nat.card F)
    (hmodel : Nonempty (G ≃* PSL2 F) ∨ Nonempty (G ≃* PGL2 F))
    (T : Sylow 2 G) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A ≤ (T : Subgroup G)) (hr : 1 < Group.rank A) :
    tau (T : Subgroup G) A = A :=
  PrimeGeometry.tau_eq_self_of_selfCentralizing T A hAT
    (twoCore_eq_bot hodd hlarge hmodel)
    (kleinFour_centralizer_eq_self hodd hmodel A (large_actor_isKleinFour hodd hmodel A hr))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.LinearWitnesses
