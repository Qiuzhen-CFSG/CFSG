module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.JankoTwoAction.Complete
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3FourAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.PSL3SevenAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Centralizer

public import Theory.ElementaryAbelian.Quotient
public import Theory.Quasithin.Rank

/-!
# The three field-component actions and the terminal rank contradiction

Each of the three actual central-quotient models forces the corrected E₉
joint residual to centralize the selected component. In ambient three-rank
at most two, every centralizing element of order three lies in the rank-two
component. Hence this E₉ lies in its center, contradicting center three-rank
at most one. No central-cover classification or full centralizer alternative
is used.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137. The E₉ residual
is the corrected joint residual retained by the existing action interfaces.
-/

public section

open Subgroup Theory.GroupTheory MulAut
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G] [Finite G]

theorem jointResidual_le_centralizer_of_component_quotient
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eR : jointResidual U f ≃* ElementaryNine)
    (hmodel : FieldComponentQuotient K) :
    jointResidual U f ≤ centralizer (K : Set G) := by
  rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact PSL3FourAction.jointResidual_le_centralizer U K f hTI hKf hn hUf e eR
  all_goals
    have hUN : U ≤ normalizer (K : Set G) :=
      hUf.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
    have hJN : jointCentralizer U f ≤ normalizer (K : Set G) :=
      inf_le_right.trans ((normal_subgroupOf_iff_le_normalizer hKf).mp hn)
    have hi := faithful_action_of_jointResidual_model U K f hTI hKf hUN eR
    have hfix := conjugation_fixes_twoPerfect U K hTI hUN
    apply jointResidual_le_centralizer_of_threeCore U K f eR hJN
  · exact JankoTwoAction.threeCoreFreeAction e _ hi hfix _
      (jointAction_range_le_centralizer U K f hUN hJN)
      (fixed_inner_le_jointAction_range U K f hKf hUN hJN)
  · exact PSL3SevenAction.threeCoreFreeAction e _ hi hfix _
      (jointAction_range_le_centralizer U K f hUN hJN)
      (fixed_inner_le_jointAction_range U K f hKf hUN hJN)

theorem jointResidual_not_le_centralizer_of_center_rank
    (U K : Subgroup G) (f : G)
    (hK : K ≤ centralizer ({f} : Set G))
    (hrank : primeRank 3 (centralizer ({f} : Set G)) ≤ 2)
    (hKrank : 2 ≤ primeRank 3 K)
    (hZ : primeRank 3 (center (K.subgroupOf (centralizer ({f} : Set G)))) ≤ 1)
    (e : jointResidual U f ≃* ElementaryNine) :
    ¬ jointResidual U f ≤ centralizer (K : Set G) := by
  intro hcent
  let B := jointResidual U f
  let H := centralizer ({f} : Set G)
  let J := K.subgroupOf H
  have hBH : B ≤ H := (map_subtype_le _).trans inf_le_right
  let A := B.subgroupOf H
  let : IsElementaryAbelian 3 ElementaryNine := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro x
      change (3 : ℕ) • x.toAdd = 0
      exact ZModModule.char_nsmul_eq_zero 3 _) }
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.subgroupOf hBH
  have hAc : Nat.card A = 3 ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv, Nat.card_congr e.toEquiv]
    simp [ElementaryNine, Nat.card_eq_fintype_card]
  have hJrank : 2 ≤ primeRank 3 J := by
    rw [primeRank_equiv 3 (subgroupOfEquivOfLe hK)]
    exact hKrank
  have hAZ : A ≤ (center J).map J.subtype := by
    intro x hx
    by_cases hx1 : x = 1
    · simp [hx1]
    have hxp : x ^ 3 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 A) (⟨x, hx⟩ : A))
    have hxo : orderOf x = 3 := by
      rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
        (orderOf_dvd_of_pow_eq_one hxp) with ho | ho
      · exact (hx1 (orderOf_eq_one_iff.mp ho)).elim
      · exact ho
    have hxc : x ∈ centralizer (J : Set H) := by
      intro y hy
      exact Subtype.ext (hcent hx y hy)
    have hxJ : x ∈ J := centralizing_three_mem hrank hJrank hxo hxc
    exact ⟨⟨x, hxJ⟩, mem_center_iff.mpr
      (fun y => Subtype.ext (hxc y y.property)), rfl⟩
  have hupper := primeRank_mono 3 hAZ
  rw [← primeRank_equiv 3 ((center J).equivMapOfInjective J.subtype J.subtype_injective)]
    at hupper
  let : IsElementaryAbelian 3 (⊤ : Subgroup A) :=
    IsElementaryAbelian.of_surjective (Subgroup.topEquiv (G := A)).symm.toMonoidHom
      (Subgroup.topEquiv (G := A)).symm.surjective
  have hlower := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup A)
    (show Nat.card (⊤ : Subgroup A) = 3 ^ 2 by simpa using hAc)
  change primeRank 3 (center J) ≤ 1 at hZ
  omega

theorem contradiction_of_component_quotient
    (U K : Subgroup G) [IsKleinFour U] [IsQuasisimple K] (f : G)
    (hTI : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup U)
    (hKf : K ≤ centralizer ({f} : Set G))
    (hn : (K.subgroupOf (centralizer ({f} : Set G))).Normal)
    (hUf : U ≤ centralizer ({f} : Set G))
    (eR : jointResidual U f ≃* ElementaryNine)
    (hmodel : FieldComponentQuotient K)
    (hrank : primeRank 3 (centralizer ({f} : Set G)) ≤ 2)
    (hKrank : 2 ≤ primeRank 3 K)
    (hZ : primeRank 3 (center (K.subgroupOf (centralizer ({f} : Set G)))) ≤ 1) :
    False :=
  jointResidual_not_le_centralizer_of_center_rank U K f hKf hrank hKrank hZ eR
    (jointResidual_le_centralizer_of_component_quotient U K f hTI hKf hn hUf eR hmodel)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
