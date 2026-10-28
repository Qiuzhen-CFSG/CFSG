module
public import Theory.GroupTheory.SpecialSixtyFourAutomorphisms
public import CFSG.Quasithin.Chapter10.SourceBlockTerminalOddRank
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.GroupTheory.PPerfectCharacteristicPair
public import Theory.GroupTheory.TwoPerfectCyclicQuotient

/-!
# Centralization of the original Borel by the linear-three overcomponent

The special two-core of order sixty-four has automorphism group of order
prime to seven. Both SL₃(4) and PSL₃(4) are quasisimple, have order divisible
by seven, and have center of order prime to seven. Their action on this
actual two-core is therefore trivial. The Borel quotient has order three;
its automorphism group is a two-group. Perfectness and the characteristic
core action then force triviality on the whole Borel subgroup.

The terminal consumer combines this with the independent cubic direction
inside the literal Borel normalizer. The earlier block geometry and linear
three recognition remain explicit source premises, but the centralization
premise of the preceding terminal rank theorem is now discharged.

Source: Aschbacher–Smith, proof of 10.2.3, printed p.747, specialized to the
four-field natural A₅ branch.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem linear_three_four_action_data (K : Subgroup G)
    (hm : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4) :
    IsQuasisimple K ∧ 7 ∣ Nat.card K ∧ ¬ 7 ∣ Nat.card (center K) := by
  rcases hm with hm | hm
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    refine ⟨IsQuasisimple.of_mulEquiv e.symm, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hF]
      norm_num
    · rw [Nat.card_congr (centerCongr e).toEquiv]
      intro hd
      have hh := hd.trans (Matrix.SL3.card_center_dvd_three F)
      norm_num at hh
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    refine ⟨IsQuasisimple.of_mulEquiv e.symm, ?_, ?_⟩
    · rw [Nat.card_congr e.toEquiv, Matrix.PSL3.LinearThree.card_projective, hF]
      norm_num
    · rw [Nat.card_congr (centerCongr e).toEquiv]
      have hz : center PSL(3,F) = ⊥ :=
        Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
      rw [hz, card_bot]
      decide

/-- The actual linear-three subgroup centralizes the normalized special two-group. -/
theorem source_linear_three_four_centralizes_special_sixty_four
    (S K : Subgroup G) [IsElementaryAbelian 2 (center S)]
    (hS : Nat.card S = 64) (hderived : commutator S = center S)
    (hZ : Nat.card (center S) = 4)
    (hm : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4)
    (hn : K ≤ normalizer (S : Set G)) : K ≤ centralizer (S : Set G) := by
  obtain ⟨hq,hseven,hZK⟩ := linear_three_four_action_data K hm
  let := hq
  exact SpecialSixtyFour.le_centralizer_of_quasisimple S K hS hderived hZ hseven hZK hn

/-- Trivial core action extends through the actual Borel quotient of order three. -/
theorem source_linear_three_four_centralizes_borel
    (A K : Subgroup G) [IsElementaryAbelian 2 (center (pCore 2 A))]
    (hS : Nat.card (pCore 2 A) = 64)
    (hderived : commutator (pCore 2 A) = center (pCore 2 A))
    (hZ : Nat.card (center (pCore 2 A)) = 4)
    (hquot : Nat.card (A ⧸ pCore 2 A) = 3)
    (hm : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4)
    (hn : K ≤ normalizer (A : Set G)) : K ≤ centralizer (A : Set G) := by
  obtain ⟨hq,hseven,hZK⟩ := linear_three_four_action_data K hm
  let := hq
  have hperfect : IsPPerfect 2 K := by
    intro N hN hp
    let := hN
    have hsub : Subsingleton (K ⧸ N) := by
      by_contra! hnt
      exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
    apply eq_top_iff.mpr
    intro k _
    exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)
  let f : K →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  let s : K →* MulAut (pCore 2 A) := (MulAut.characteristic (pCore 2 A)).comp f
  have hs : s = 1 := SpecialSixtyFour.hom_eq_one_of_quasisimple hS hderived hZ hseven hZK s
  have hc : K ≤ centralizer (A.pCoreIn 2 : Set G) := by
    intro k hk x hx
    obtain ⟨y,hy,rfl⟩ := hx
    have he := congrArg (fun a : K →* MulAut (pCore 2 A) =>
      (((a ⟨k,hk⟩ ⟨y,hy⟩ : pCore 2 A) : A) : G)) hs
    change k * (y : G) * k⁻¹ = (y : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact le_centralizer_of_pPerfect_of_core A K hperfect hn hc
    (commutator_le_pCoreIn_of_twoPerfect_of_normalizes_of_quotient_card_three A K hperfect hn hquot)

/-- The terminal source contradiction no longer assumes Borel centralization. -/
theorem source_block_borel_contradiction_of_special_core
    {𝒦 : GroupClass} (D K S : Subgroup G)
    [IsElementaryAbelian 2 (center (pCore 2 (S ⊔ D : Subgroup G)))]
    (hI : IsSQTK 𝒦 (normalizer ((S ⊔ D : Subgroup G) : Set G)))
    (hfaithful : D ⊓ centralizer (S : Set G) = ⊥)
    (hD : Nat.card D = 3)
    (hS : Nat.card (pCore 2 (S ⊔ D : Subgroup G)) = 64)
    (hderived : commutator (pCore 2 (S ⊔ D : Subgroup G)) =
      center (pCore 2 (S ⊔ D : Subgroup G)))
    (hZ : Nat.card (center (pCore 2 (S ⊔ D : Subgroup G))) = 4)
    (hquot : Nat.card ((S ⊔ D : Subgroup G) ⧸ pCore 2 (S ⊔ D : Subgroup G)) = 3)
    (hm : IsSL K 3 4 ∨ ClassicalGroup.IsPSL K 3 4)
    (hn : K ≤ normalizer ((S ⊔ D : Subgroup G) : Set G)) : False := by
  exact source_block_borel_normalizer_contradiction D K S hI hfaithful
    (source_linear_three_four_centralizes_borel (S ⊔ D) K hS hderived hZ hquot hm hn)
    hD hm

end CFSG.Quasithin.Chapter10
