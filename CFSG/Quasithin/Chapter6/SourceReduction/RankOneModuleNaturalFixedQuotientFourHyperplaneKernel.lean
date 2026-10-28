module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourWeakClosure
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpace
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# The actual Sylow centralizer of a Hermitian binary hyperplane

A nontrivial two-subgroup of the faithful original quotient contains an
involution. Fixing a binary hyperplane would give its cyclic actor fixed
codimension at most one, contrary to the marked Hermitian calculation when
the half-degree exceeds one. Literal subgroup-space coordinates transport
the original index-two condition to this fixed-codimension bound.

Thus C_T(U) = C_T(W) for every binary hyperplane U of the original Hermitian
module W. On the original moved layer this is exactly O₂(LT).
Source: Aschbacher–Smith, 6.1.4, printed p.665.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
open ChapterK.RankOne Representation.OrthogonalFourMinus.FiniteModel

local instance hyperplaneFixedAlgebra (s : ℕ) : Algebra (ZMod 2) (fixedField s) :=
  ZMod.algebra _ 2
local instance hyperplaneBinaryModule (s : ℕ) [NeZero s] : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

private theorem marked_two_subgroup_fixing_hyperplane_eq_bot
    {D X : Type*} [Group D] [Finite D] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    {s : ℕ} [NeZero s] {ρ : Representation (ZMod 2) D X} {B : Subgroup D}
    (h : SourceHypotheses ρ B) (M : OrthogonalModel s ρ B) (hs : 1 < s)
    (A : Subgroup D) (hA : IsPGroup 2 A) (hcodim : fixedCodim ρ A ≤ 1) :
    A = ⊥ := by
  rcases hA.card_eq_or_dvd with hcard | hdiv
  · exact card_eq_one.mp hcard
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdiv
  have ha' : orderOf (a : D) = 2 := by
    rwa [←orderOf_injective A.subtype A.subtype_injective] at ha
  obtain ⟨he,hr,_,_⟩ := involution_actor_rank_and_fixedCodim ρ a ha'
  have hc : fixedCodim ρ (zpowers (a : D)) ≤ 1 :=
    (NaturalTensor.fixedCodim_mono ρ (zpowers_le.mpr a.property)).trans hcodim
  have hcases := FourOffender.marked_near_offender_cases h M hs (zpowers (a : D)) he
    (by omega)
  rcases hcases.2.2.2 with hh | hh <;> omega

private theorem fixedCodim_le_one_of_centralizes_hyperplane
    {H D : Type*} [Group H] [Finite H] [Group D]
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (q : H →* D) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (W : Set H))
    (U C : Subgroup H) (hc : C ≤ centralizer (U : Set H))
    (hidx : U.relIndex W = 2) :
    fixedCodim (NormalElementaryQuotient.representation W q hq hk) (C.map q) ≤ 1 := by
  let P := NormalElementaryQuotient.subgroupSpace W U
  have hfix := NormalElementaryQuotient.subgroupSpace_fixed_of_centralizes W q hq hk U C hc
  have hp : Nat.card (U.subgroupOf W) = 2 ^ Module.finrank (ZMod 2) P := by
    change Nat.card P = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  have hw : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [←Nat.card_congr (Additive.toMul : Additive W ≃ W)]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  have hprod := (U.subgroupOf W).card_mul_index
  rw [hp,show (U.subgroupOf W).index = 2 from hidx,hw,←pow_succ] at hprod
  have hdim := Nat.pow_right_injective (by decide : 2 ≤ 2) hprod
  have hle := Submodule.finrank_mono hfix
  have hsum := fixedCodim_add_finrank
    (NormalElementaryQuotient.representation W q hq hk) (C.map q)
  change Module.finrank (ZMod 2) P ≤ _ at hle
  omega

namespace RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W : Subgroup G} {n s : ℕ} [NeZero s]

/-- A binary hyperplane of the actual Hermitian module has exactly the
same Sylow centralizer as the whole original module. -/
theorem Input.hermitian_hyperplane_sylow_centralizer
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (U : Subgroup G) (hUW : U ≤ W) (hcor : ChapterE.subgroupCorank W U = 1) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      (T : Subgroup G) ⊓ centralizer (W : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let W0 := W.subgroupOf J
  let U0 := U.subgroupOf J
  let C := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let C0 := C.subgroupOf J
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  let := h.reduced.2.1
  let q := QuotientGroup.mk' (pCore 2 J)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : q.ker = centralizer (W0 : Set J) :=
    (QuotientGroup.ker_mk' _).trans h.reduced_centralizer_core.symm
  let ρ := NormalElementaryQuotient.representation W0 q hq hk
  have hidx : U.relIndex W = 2 := by
    rw [W.relIndex_eq_two_pow_quotient_finrank U,
      ←ChapterE.subgroupCorank_eq_quotient_finrank,hcor]
    rfl
  have hidx0 : U0.relIndex W0 = 2 := (relIndex_subgroupOf h.reduced.1).trans hidx
  have hc0 : C0 ≤ centralizer (U0 : Set J) := by
    intro c hc u hu
    apply Subtype.ext
    exact hc.2 u.val hu
  have hcodim := fixedCodim_le_one_of_centralizes_hyperplane W0 q hq hk U0 C0 hc0 hidx0
  have hC0S : C0 ≤ (S : Subgroup J) := fun _ hx => hx.1
  have hP : IsPGroup 2 (C0.map q) := (S.isPGroup'.to_le hC0S).map q
  obtain ⟨hsource,⟨M⟩⟩ := h.hermitian_original_source hm
  have hz : C0.map q = ⊥ :=
    marked_two_subgroup_fixing_hyperplane_eq_bot hsource M hs _ hP hcodim
  have hC0 : C0 ≤ centralizer (W0 : Set J) := hk ▸ (map_eq_bot_iff C0).mp hz
  apply le_antisymm
  · intro c hc
    refine ⟨hc.1,?_⟩
    intro w hw
    exact congrArg J.subtype (hC0
      (show (⟨c,(show (T : Subgroup G) ≤ J from le_sup_right) hc.1⟩ : J) ∈ C0 from hc)
      ⟨w,h.reduced.1 hw⟩ hw)
  · exact inf_le_inf_left _ (centralizer_le hUW)

end RankOneGeneric

namespace RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n s : ℕ} [NeZero s]

/-- Every binary hyperplane of the original Hermitian moved layer has
Sylow centralizer exactly O₂(LT). All quotient-action conditions are derived. -/
theorem original_hermitian_hyperplane_sylow_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (layer L V) (SL2.BinarySmall.hermitian s)) (hs : 1 < s)
    (U : Subgroup G) (hU : U ≤ layer L V)
    (hcor : ChapterE.subgroupCorank (layer L V) U = 1) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [(h.rankOneInput hout).commutator_input.hermitian_hyperplane_sylow_centralizer hm hs U hU hcor]
  exact original_hermitian_layer_sylow_centralizer h hm

end RankOneRecognition
end CFSG.Quasithin.Chapter6.Source
