module

public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.Configurations.LinearBudget
public import Theory.Representation.BinaryGroupAction
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.GroupAction.SixteenOddComplements.Nine

/-!
# The core and group in the four-dimensional configuration

A faithful elementary three-core on a binary four-space has order at most
nine: its order divides the checked order of GL₄(2), whose three-part is
nine. The reduced rank alternatives therefore give rank two. Conjugation
by the original four-group is faithful, so the actual complementary
subgroups identify the original group with S₃ × S₃.

These are the unmarked group deductions in Aschbacher--Smith D.2.14,
printed p.187. They do not assert existence, transitivity or diagonal
marking of the two support factors.
-/

public section
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.FittingConfigurations
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
/-- The faithful four-dimensional module excludes the rank-three core. -/
theorem Reduced.core_rank_eq_two_of_finrank_four {P A : Subgroup G} {s : ℕ}
    (h : Reduced ρ P A s) (hdim : Module.finrank (ZMod 2) V = 4) : s = 2 := by
  let := Representation.BinaryGroupAction.action ρ
  let := Representation.BinaryGroupAction.elementary (V := V)
  let f := (MulDistribMulAction.toMulAut G (Multiplicative V)).comp P.subtype
  have hi : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply h.faithful
    ext v
    exact congrArg Multiplicative.toAdd
      (MulEquiv.congr_fun he (Multiplicative.ofAdd v))
  have hc : Nat.card (Multiplicative V) = 2 ^ 4 := by
    change Nat.card V = 2 ^ 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hd := Subgroup.card_dvd_of_injective f hi
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow
    (Multiplicative V) 4 hc, h.card_core] at hd
  rcases h.rank_cases with hs | hs
  · exact hs
  · rw [hs] at hd
    norm_num [Fin.prod_univ_succ] at hd

omit [FiniteDimensional (ZMod 2) V] in
/-- Recognition uses the actual conjugation action and complementary core and actor. -/
theorem Reduced.nonempty_symmetricThree_product_of_rank_two
    {P A : Subgroup G} {s : ℕ} (h : Reduced ρ P A s)
    (hs : s = 2) :
    Nonempty (G ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let : P.Normal := h.normal
  let : IsElementaryAbelian 3 P := h.elementary
  let : IsElementaryAbelian 2 A := h.starred.1.2.1.2
  have hP : Nat.card P = 9 := by rw [h.card_core, hs]; rfl
  have hn : A ≤ Subgroup.normalizer (P : Set G) := by
    rw [P.normalizer_eq_top]
    exact le_top
  let f : A →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_one f).mpr
    intro a ha
    have hk : Subgroup.inclusion hn a ∈ P.normalizerMonoidHom.ker := ha
    rw [Subgroup.normalizerMonoidHom_ker] at hk
    exact Subtype.ext (h.actor_faithful.le ⟨a.property, hk⟩)
  have hd : Disjoint P A := Subgroup.disjoint_of_coprime_natCard
    (by rw [hP, h.card_actor]; decide)
  have hcomp : P.IsComplement' A := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left P A hn, h.generated]
    rfl
  obtain ⟨L, hL, hLi⟩ := SixteenOddComplements.invariant_three_of_four_action
    f hf hP h.card_actor
  obtain ⟨e⟩ := ElementaryNineFourSemidirect.nonempty_mulEquiv
    f hP h.card_actor hf L hL hLi
  exact ⟨(SemidirectProduct.mulEquivSubgroup hcomp).symm.trans e⟩
end CFSG.Quasithin.ChapterD.FittingConfigurations
