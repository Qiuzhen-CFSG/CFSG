module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Normalizer
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.Quotients

/-!
# The actual normalizer section in Lemma 14.4.9

Apply the proved symmetric fixed-line argument to the literal lift D,
then identify UD/D inside N_G(D)/O₂(N_G(D)). Both the denominator's
relative normality and the map on representatives are retained. The
selection, extraspecial calculations and containing component remain
separate source obligations.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

/-- The symmetric lift data construct the section through the genuine
normalizer quotient; there is no extra core-intersection hypothesis. -/
theorem source_normalizer_section
    (U : Subgroup G) (z x : G) (hz : orderOf z = 2)
    (hU : IsPGroup 2 U)
    (hD : IsElementaryAbelian 2 (centralizerLift U z (conjugateElement z x)))
    (hY : symmetricActor U z x ≤
      normalizer (centralizerLift U z (conjugateElement z x) : Set G))
    (hCU : centralizerLift U z (conjugateElement z x) ⊓ centralizer (U : Set G) =
      zpowers z)
    (hCUx : centralizerLift U z (conjugateElement z x) ⊓
      centralizer (conjugateCore U x : Set G) = zpowers (conjugateElement z x))
    (hself : (U ⊔ centralizerLift U z (conjugateElement z x)) ⊓
      centralizer (centralizerLift U z (conjugateElement z x) : Set G) =
        centralizerLift U z (conjugateElement z x)) :
    let D := centralizerLift U z (conjugateElement z x)
    let N := normalizer (D : Set G)
    let V := U ⊔ D
    ∃ (hVN : V ≤ N) (hDV : (D.subgroupOf V).Normal),
      letI := hDV
      ∃ e : (V ⧸ D.subgroupOf V) ≃* (localSectionMap N V hVN).range,
        ∀ v : V, (e (QuotientGroup.mk' (D.subgroupOf V) v) : N ⧸ pCore 2 N) =
          localSectionMap N V hVN v := by
  let D := centralizerLift U z (conjugateElement z x)
  let N := normalizer (D : Set G)
  let V := U ⊔ D
  have hVN : V ≤ N := sup_le
    ((show U ≤ symmetricActor U z x from le_sup_right.trans le_sup_left).trans hY)
    D.le_normalizer
  have hDV : (D.subgroupOf V).Normal := normal_subgroupOf_of_le_normalizer hVN
  let := hDV
  have hinter : V ⊓ N.pCoreIn 2 = D :=
    (lift_normalizer_core U z x hz hU hD hY hCU hCUx hself).2.2
  exact ⟨hVN, hDV, normalizerSectionEquiv N V D hVN hinter,
    normalizerSectionEquiv_mk N V D hVN hinter⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve
