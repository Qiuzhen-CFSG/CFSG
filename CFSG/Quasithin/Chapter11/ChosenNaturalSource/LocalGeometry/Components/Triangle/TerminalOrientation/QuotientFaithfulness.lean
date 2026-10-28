module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank

/-!
# Faithfulness of the original cubic actors on the PSL₃(4) section

A subgroup centralizing K/O₂(K) has additive three-rank with K, because
that quotient is centerless. Its rank is therefore zero in the source's
two-local group, whereas every nontrivial subgroup of the original Cartan
has positive three-rank. This proves that the Cartan's action kernel on
K/O₂(K) is trivial, retaining the full intrinsic two-core and the actual
ambient actor. In particular the canonical cubic X₁ has noncentral action.
This whole-section calculation precedes the comparison with K₀/O₂(K₀).
Source: Aschbacher--Smith, 11.1.2, printed pp.762--764; A.3.18.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Cubic rank two detects every nonidentity cubic actor on the entire
PSL₃(4) two-core section. Normality is only needed in the actor's join. -/
theorem projective_four_cubic_kernel_eq_bot (K X : Subgroup G)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hX : IsPGroup 3 X) (hr : primeRank 3 (X ⊔ K : Subgroup G) ≤ 2) :
    X ⊓ Closure.coreQuotientCentralizer K = ⊥ := by
  let A := X ⊓ Closure.coreQuotientCentralizer K
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    apply e.map_eq_one_iff.mp
    exact (Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 3) F)).le
      ((centerCongr e) ⟨x,hx⟩).property
  have hcop : Nat.Coprime 3 (Nat.card (center (K ⧸ pCore 2 K))) := by
    rw [hz,card_bot]
    decide
  have hrK : 2 ≤ primeRank 3 K := by
    have hh := Theory.SpecificGroups.SignedThreeCubicRank.linear_projective
      (show Nat.card F = 2^2 by simpa using hF) (by decide : Even 2)
    rw [←primeRank_congr 3 e] at hh
    exact hh.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)
  have hn : A ≤ normalizer (K : Set G) :=
    inf_le_right.trans (map_subtype_le _)
  have hc : ⁅(pResidual 2 A).map A.subtype,K⁆ ≤ K.pCoreIn 2 := by
    apply commutator_le.mpr
    intro a ha k hk
    exact Closure.coreQuotientCentralizer_commutator ((map_subtype_le _ ha).2) hk
  have hh := ResidualCentralizerRank.primeRank_sum_le_of_normalized_factor
    (by decide : Odd 3) A K hn hc hcop
  have hu : primeRank 3 (A ⊔ K : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 (sup_le_sup_right (show A ≤ X from inf_le_left) K)).trans hr
  have he : primeRank 3 A = 0 := by omega
  exact card_eq_one.mp ((hX.to_le (show A ≤ X from inf_le_left)).card_eq_or_dvd.resolve_right
    (PrimeRank.eq_zero_iff_not_dvd_card.mp he))

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The actual original flag normalizer supplies the rank bound. The
kernel is that of X on the full quotient K/O₂(K), without an action premise. -/
theorem first_projective_cartan_kernel_eq_bot (hu : f.IsInnerUnique)
    (hd : S.field.degree = 2) {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    X ⊓ Closure.coreQuotientCentralizer K = ⊥ := by
  have hthree : IsPGroup 3 X := IsPGroup.of_card (n := 2) (by
    rw [c.cartan_card hX,hd]
    norm_num)
  have hn : X ⊔ K ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le (f.cartan_normalizes hu hX 0) hK.1.1
  have hr : primeRank 3 (X ⊔ K : Subgroup G) ≤ 2 :=
    (primeRank_mono 3 hn).trans
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
        3 Nat.prime_three (by decide))
  exact projective_four_cubic_kernel_eq_bot K X hk hthree hr

/-- Every literal order-three subgroup of the original Cartan acts
nontrivially on the whole containing component's two-core quotient. -/
theorem first_projective_cubic_not_central (hu : f.IsInnerUnique)
    (hd : S.field.degree = 2) {K X E : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hEX : E ≤ X) (hE : Nat.card E = 3) :
    ¬ E ≤ Closure.coreQuotientCentralizer K := by
  intro hc
  have he : E = ⊥ := bot_unique ((le_inf hEX hc).trans
    (first_projective_cartan_kernel_eq_bot D S f hu hd hX hK hk).le)
  rw [he,card_bot] at hE
  contradiction

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.TerminalOrientation
