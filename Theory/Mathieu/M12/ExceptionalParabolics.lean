module

public import Theory.Mathieu.M12.ValueBoundParabolics
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.SpecificGroups.SL2.BinaryProjective
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The marked M₁₂ exceptional amalgam

The centralizer of the distinguished involution and the normalizer of its
marked natural four generate the actual Witt-design M₁₂. Their common
Sylow subgroup is self-normalizing in both parabolics, so their inclusion
amalgam has the whole Borel as overlap. Both intrinsic two-core quotients
are PSL₂(2). The first core is the specified quaternion central product,
and the second core has order 32.

The quotient and quaternion-factor calculations are reused from the concrete
small parabolic pair. An index-three argument gives the local normalizers:
a larger normalizer would make the Sylow subgroup normal, contradicting
the already computed two-core order.

Source: Aschbacher--Smith, F.1.12(I)(12), printed p.263 (PDF p.274), with
the first denominator and quaternion core corrected to refer to L₁.
Notation E.2.16, printed p.228, uses Q₈² for Q₈ * Q₈, of order 32.
This is a concrete model construction, not a uniqueness theorem.
-/

public section
noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics
open Subgroup Theory.GroupTheory ValueBoundParabolics

/-- The actual embedded quaternion factors in the intrinsic first two-core. -/
def firstCoreQuaternionData : QuaternionCentralProductData (pCore 2 firstParabolic) :=
  coreQuaternionData.map firstCoreEquiv.symm

theorem firstCore_card : Nat.card (pCore 2 firstParabolic) = 32 :=
  firstCoreQuaternionData.card

theorem firstCore_extraspecial : IsExtraspecial 2 (pCore 2 firstParabolic) :=
  firstCoreQuaternionData.extraspecial

theorem secondCore_card : Nat.card (pCore 2 secondParabolic) = 32 := by
  have h := (pCore 2 secondParabolic).index_mul_card
  have hq : (pCore 2 secondParabolic).index = 6 := by
    rw [Subgroup.index_eq_card, Nat.card_congr secondCoreQuotient.toEquiv,
      Nat.card_perm, Nat.card_fin]
    decide
  rw [hq, card_secondParabolic] at h
  omega

private def permThreeEquivPSL : Equiv.Perm (Fin 3) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm.trans
    Matrix.SpecialLinearGroup.sl2TwoEquivPSL2Two

/-- The first quotient has its own intrinsic two-core as denominator. -/
def firstPSLQuotient : (firstParabolic ⧸ pCore 2 firstParabolic) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  firstCoreQuotient.trans permThreeEquivPSL

/-- The second quotient also has its own intrinsic two-core as denominator. -/
def secondPSLQuotient : (secondParabolic ⧸ pCore 2 secondParabolic) ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  secondCoreQuotient.trans permThreeEquivPSL

private theorem local_normalizer {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (hc : Nat.card G = 192)
    (hT : Nat.card T = 64) (hQ : Nat.card (pCore 2 G) = 32) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) = T := by
  have hi : (T : Subgroup G).index = 3 := by
    have h := (T : Subgroup G).index_mul_card
    rw [hc, hT] at h
    omega
  have hd := Subgroup.index_dvd_of_le (T : Subgroup G).le_normalizer
  rw [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · have hn : (T : Subgroup G).Normal :=
      Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h)
    have hl : (T : Subgroup G) ≤ pCore 2 G := le_sSup ⟨hn, T.isPGroup'⟩
    have hb := Subgroup.card_le_of_le hl
    rw [hT, hQ] at hb
    omega
  · apply (Subgroup.eq_of_le_of_card_ge (T : Subgroup G).le_normalizer _).symm
    have hm := (Subgroup.normalizer ((T : Subgroup G) : Set G)).index_mul_card
    rw [h, hc] at hm
    rw [hT]
    omega

private theorem relative_normalizer (H : Subgroup M12) (hS : sylowCandidate ≤ H)
    (hc : Nat.card H = 192) (hQ : Nat.card (pCore 2 H) = 32) :
    H ⊓ Subgroup.normalizer (sylowCandidate : Set M12) = sylowCandidate := by
  let T := commonSylow.subtype hS
  have hT : Nat.card T = 64 := by
    change Nat.card (sylowCandidate.subgroupOf H) = 64
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv]
    exact card_sylowCandidate
  have h := local_normalizer T hc hT hQ
  change Subgroup.normalizer (sylowCandidate.subgroupOf H : Set H) =
    sylowCandidate.subgroupOf H at h
  rw [← Subgroup.subgroupOf_normalizer_eq hS] at h
  ext g
  constructor
  · rintro ⟨hg, hn⟩
    exact (show (⟨g,hg⟩ : H) ∈ sylowCandidate.subgroupOf H from h ▸ hn)
  · intro hg
    exact ⟨hS hg, Subgroup.le_normalizer hg⟩

theorem first_sylow_normalizer :
    firstParabolic ⊓ Subgroup.normalizer (sylowCandidate : Set M12) = sylowCandidate :=
  relative_normalizer firstParabolic inf_le_left card_firstParabolic firstCore_card

theorem second_sylow_normalizer :
    secondParabolic ⊓ Subgroup.normalizer (sylowCandidate : Set M12) = sylowCandidate :=
  relative_normalizer secondParabolic inf_le_right card_secondParabolic secondCore_card

/-- The inclusion maps retain the entire, literal common overlap. -/
@[expose] def amalgam : RankTwoAmalgam firstParabolic sylowCandidate secondParabolic :=
  RankTwoAmalgam.ofSubgroups _ _ _ inf_le_left inf_le_right

theorem amalgam_left_injective : Function.Injective amalgam.left :=
  Subgroup.inclusion_injective inf_le_left

theorem amalgam_right_injective : Function.Injective amalgam.right :=
  Subgroup.inclusion_injective inf_le_right

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics
