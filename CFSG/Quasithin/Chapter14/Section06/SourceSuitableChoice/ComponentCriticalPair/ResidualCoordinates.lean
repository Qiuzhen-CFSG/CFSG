module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.CentralLine
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.Lift

/-!
# The terminal residual coordinates from the dual quotient calculation

This conditional source consumer uses the original rank-two data, H=Mc and
the same suitable u. It constructs W=[B,O^2(C_H(u mod Z))] and a=u*c, and
applies the coordinates to rank four and escape from M. The central-line
containment is proved here from source 14.6.2 on B. The three quotient image
premises, the seed projections and the terminal numerical bounds still need
their natural/dual module proofs before the source endgame is complete.

Source: Aschbacher--Smith, 14.6.20--24 and the final paragraph on printed p.1042.
-/

public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Conditional source assembly of the moving eight-group. Only the quotient
image calculations remain; no coordinates or rank conclusion are assumed. -/
theorem source_residual_span_of_dual_images
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B C : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hCU : C ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ (B ⊔ C) ≤ centralInvolutions T)
    (hfixed : ∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ centralInvolutions T)
    (u b c v : G) (huA : u ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hv : v ∈ localModule T M) (hvZ : v ∉ centralInvolutions T)
    (hseed : v * (u * b * c)⁻¹ ∈ centralInvolutions T)
    {E : Type*} [Group E] (q : B →* E) (hk : q.ker = (centralInvolutions T).subgroupOf B) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let P := h.kernel (zpowers u)
    let R := (pResidual 2 P).map P.subtype
    ComponentSupports.Suitable h Mc u →
    P ≤ normalizer (B : Set G) →
    R ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc →
    Nat.card ((⁅B,R⁆.subgroupOf B).map q) = 4 →
    q ⟨b,hb⟩ ∈ (⁅B,R⁆.subgroupOf B).map q →
    (⁅B,R⁆.subgroupOf B).map q ≤
      ((closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆}).subgroupOf B).map q →
    ∃ d : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T) R,
      d.W = ⁅B,R⁆ ∧ d.a = u*c ∧ d.b = b ∧
      primeRank 2 (conjugateSpanBy (localModule T M) R) = 4 ∧ ¬R ≤ M := by
  dsimp only
  intro hu hn hRF himage hbimage hgenerate
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let P := h.kernel (zpowers u)
  let R := (pResidual 2 P).map P.subtype
  have hne : ⁅B,R⁆ ≠ ⊥ := by
    intro hz
    change Nat.card ((⁅B,R⁆.subgroupOf B).map q) = 4 at himage
    norm_num only [hz, bot_subgroupOf, Subgroup.map_bot, card_bot] at himage
  have hline := source_point_le_dual_residual hG T hempty hM hunique hmany hcard e hab
    B hBU u hu hn hRF hne
  have huZ : u ∉ centralInvolutions T := by
    intro hz
    apply hu.2.2.2.1
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (h.H_centralizes (pCoreIn_le 2 Mc hx) u hz).symm
  let := h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  let d := residual_span_coordinates_of_section_images h hcard A B C hAU hBU hCU
    hsep hfixed u b c v huA huZ hb hc hv hvZ hseed q hk
    ((map_subtype_le _).trans hn) hline himage hbimage hgenerate
  exact ⟨d,rfl,rfl,rfl,d.rank_four,source_residual_not_le_of_span_coordinates T hcard P d⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
