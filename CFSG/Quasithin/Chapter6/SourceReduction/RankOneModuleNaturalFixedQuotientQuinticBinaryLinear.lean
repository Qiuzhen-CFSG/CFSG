module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveFactor
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.ThreeFree

/-!
# Excluding the original binary linear four- and five-space carriers

The actual effective component action gives a faithful quintic subgroup
whose join with a full Sylow has order dividing a power of two times five.
The binary linear outer quotient is a two-group, so this action is detected
in an actual full-Sylow overgroup of the same component. The native flag
theorem makes every three-free overgroup equal to its Sylow, excluding five.

Source: Aschbacher--Smith 6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- Both binary projective linear rows of Theorem C are excluded on the
original outside component, with the same literal central quotient. -/
theorem original_hermitian_component_not_binary_linear
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (r : ℕ) (hr : r = 4 ∨ r = 5) :
    ¬ ClassicalGroup.IsPSL (coreCentralQuotient K) r 2 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let A := coreCentralActorImage K M₁
  let N := (MulAut.innerSubgroup (coreCentralQuotient K)).subgroupOf A
  obtain ⟨E,S,a,hN,⟨eN⟩,hE,hC,hcard⟩ :=
    original_hermitian_quintic_effective_factor h hout hm hM₁ hCM₁ hK hnot hq
  let : N.Normal := hN
  let f : N ≃* SL(r,ZMod 2) :=
    ((eN.trans e).trans (Atlas.fieldEquivPSL r eF)).trans (projectiveEquivSL (by omega))
  have hz : center N = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr f ⟨x,hx⟩).property
    change f x ∈ center SL(r,ZMod 2) at hh
    rw [binary_center_eq_bot (by omega),mem_bot] at hh
    exact f.map_eq_one_iff.mp hh
  apply no_odd_actor_of_sylow_order_bound N E S (by decide : Odd 5) hz
    ((sl_outer_isTwoGroup hr).of_equiv (MulAut.outerCongr f).symm) _ hE
    (by rw [hC]; exact disjoint_bot_right) hcard
  intro P J hJ hPJ h5
  let g := f.trans (slEquivLinear r)
  let : Finite (LinearGroup r) := Finite.of_equiv N g.toEquiv
  let Q := P.mapSurjective (f := g.toMonoidHom) g.surjective
  let H := J.map g.toMonoidHom
  have h3 : ¬3 ∣ Nat.card H := by
    rw [card_map_of_injective g.injective]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      ((((by decide : Nat.Coprime 3 2).pow_right a).mul_right
        (by decide : Nat.Coprime 3 5)).of_dvd_right hJ)
  have hQH : (Q : Subgroup (LinearGroup r)) ≤ H := map_mono hPJ
  have hH : H = (Q : Subgroup (LinearGroup r)) := by
    rcases hr with rfl | rfl <;>
      exact BinaryLinear.SylowFlagOvergroups.eq_sylow_of_not_three_dvd Q H hQH h3
  have hH5 : 5 ∣ Nat.card H := by rwa [card_map_of_injective g.injective]
  obtain ⟨b,hb⟩ := Q.isPGroup'.exists_card_eq
  rw [hH,hb] at hH5
  exact (by decide : ¬5 ∣ 2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hH5)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
