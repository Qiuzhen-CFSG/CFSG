module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki.Model
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.SpecificGroups.Suzuki.CyclicOuter
public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The original actor and its Suzuki Sylow subgroup

Self-centralization of F* and centerlessness of the specified Suzuki layer
embed G/L in the actual outer automorphism group. Its odd order places every
two-subgroup inside L. Simplicity and even order identify L with O^{2′}(G),
using the prime-to-two residual convention. Sylow restriction and the literal
subtype map then give the rank and elementary structure of Ω₁(T) in G.

Source: Aschbacher–Smith, K.3.6, printed p.457 (1 March 2004 manuscript).
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki BenderSuzuki.MatrixGroups Subgroup
open Representation.BinaryOffender Theory.GroupTheory

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {m : ℕ} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace SourceHypotheses
variable (h : SourceHypotheses ρ L) (M : SuzukiModel m ρ L) (hm : 1 ≤ m)
include M hm

omit [Finite G] in
/-- The full outer group of the specified layer has odd order. -/
theorem suzuki_outer_odd : Odd (Nat.card (MulAut.Outer L)) := by
  rw [Nat.card_congr (MulAut.outerCongr M.groupEquiv).toEquiv]
  exact suzuki_odd_outer_index m hm

omit [Finite G] in
/-- In particular every permitted outer action has odd order. -/
theorem suzuki_outer_order_odd (a : MulAut.Outer L) : Odd (orderOf a) :=
  (suzuki_outer_odd M hm).of_dvd_nat (orderOf_dvd_natCard a)

omit [Finite G] in
private theorem suzuki_layer_simple : IsSimpleGroup L := by
  have hs : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  let := hs.isSimple
  exact M.groupEquiv.isSimpleGroup

include h

/-- Self-centralization is used in G, not in a full linear normalizer. -/
theorem suzuki_centralizer_eq_bot : centralizer (L : Set G) = ⊥ := by
  have hs : IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
    .isSuzuki ⟨m, hm, ⟨MulEquiv.refl _⟩⟩
  let : IsSimpleGroup (SuzukiMatrixGroup m) := hs.isSimple
  let : IsSimpleGroup L := M.groupEquiv.isSimpleGroup
  have hc : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact False.elim (hs.not_commutative (fun x y => by
        have hx : M.groupEquiv.symm x ∈ center L := by rw [hc]; trivial
        have he := (mem_center_iff.mp hx (M.groupEquiv.symm y)).symm
        simpa using congrArg M.groupEquiv he))
  have hCL : centralizer (L : Set G) ≤ L := by
    rw [← h.fitting]
    exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  apply bot_unique
  intro g hg
  have hgZ : (⟨g, hCL hg⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    intro x
    exact Subtype.ext (hg x x.property)
  rw [hc] at hgZ
  exact congrArg Subtype.val (mem_bot.mp hgZ)

/-- The quotient of the actual source actor by its layer has odd order. -/
theorem suzuki_odd_index : Odd L.index := by
  let : L.Normal := h.layer_normal
  exact (suzuki_outer_odd M hm).of_dvd_nat
    (card_dvd_of_injective (MulAut.outerAction L)
      (MulAut.outerAction_injective L (h.suzuki_centralizer_eq_bot M hm)))

/-- Oddness is on the literal quotient G/L. Its normality is deduced from F*. -/
theorem suzuki_quotient_odd :
    letI : L.Normal := h.layer_normal
    Odd (Nat.card (G ⧸ L)) := h.suzuki_odd_index M hm

/-- The source O^{2′}(G) identity, with the repository's exact convention. -/
theorem suzuki_primeToResidual : primeToResidual 2 G = L := by
  let : L.Normal := h.layer_normal
  let : IsSimpleGroup L := suzuki_layer_simple M hm
  have hres : primeToResidual 2 L = ⊤ := by
    rcases (inferInstance : (primeToResidual 2 L).Normal).eq_bot_or_eq_top with hb | ht
    · have hc := primeToResidual_index_coprime (G := L) 2
      rw [hb, index_bot] at hc
      let P : Sylow 2 L := Classical.choice inferInstance
      have hd : 2 ∣ Nat.card L := by
        apply dvd_trans (b := Nat.card (omegaOneAmbient (P : Subgroup L)))
        · rw [suzukiSylow_omega_card (by omega) M.groupEquiv P]
          exact dvd_pow_self 2 (by omega : 2 * m + 1 ≠ 0)
        · exact (omegaOneAmbient (P : Subgroup L)).card_subgroup_dvd_card
      exact (Nat.prime_two.coprime_iff_not_dvd.mp hc hd).elim
    · exact ht
  exact le_antisymm (primeToResidual_le L (h.suzuki_odd_index M hm).coprime_two_left)
    (le_primeToResidual_of_eq_top 2 L hres)

/-- Every Sylow two-subgroup lies in the original marked layer. -/
theorem suzuki_sylow_le (T : Sylow 2 G) : (T : Subgroup G) ≤ L := by
  rw [← h.suzuki_primeToResidual M hm]
  intro x hx
  obtain ⟨n, hn⟩ := T.isPGroup' ⟨x, hx⟩
  exact mem_primeToResidual_of_pow (congrArg Subtype.val hn)

/-- The first omega in G is elementary and has the source rank r=2m+1. -/
theorem suzuki_omega_calculation (T : Sylow 2 G) :
    IsElementaryTwo (omegaOneAmbient (T : Subgroup G)) ∧
    rank (omegaOneAmbient (T : Subgroup G)) = 2 * m + 1 := by
  let : L.Normal := h.layer_normal
  obtain ⟨P, hP⟩ := T.exists_sylow_map_eq_inf_of_normal L
  rw [inf_eq_left.mpr (h.suzuki_sylow_le M hm T)] at hP
  have he := suzukiSylow_omega_elementary (by omega) M.groupEquiv P
  have hc : Nat.card (omegaOneAmbient (T : Subgroup G)) = 2 ^ (2 * m + 1) := by
    rw [← hP, ← map_omegaOneAmbient_injective L.subtype L.subtype_injective,
      card_map_of_injective L.subtype_injective]
    exact suzukiSylow_omega_card (by omega) M.groupEquiv P
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hb
    rw [hb, card_bot] at hc
    have hp := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : 2 * m + 1 ≠ 0)
    omega
  · rw [← hP, ← map_omegaOneAmbient_injective L.subtype L.subtype_injective]
    let := he
    exact IsElementaryAbelian.map _
  · rw [rank, hc, Nat.log_pow (by decide : 1 < 2)]

end SourceHypotheses
end CFSG.Quasithin.ChapterK.RankOne
