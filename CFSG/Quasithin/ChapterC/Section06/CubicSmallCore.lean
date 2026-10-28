module
public import CFSG.Quasithin.ChapterC.Section06.RankOneSource
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.CubicModel
public import Theory.GroupTheory.PGroup.SelfCentralizingFour

/-!
# The small-core A₃ branch of C.6.1

If the original two-core Q equals the single A₃ module U, then U is a
four-group. The original normalizer condition gives N_Λ(U)=R, while the
literal core-centralizer theorem gives C_R(U)=U. Thus U is self-centralizing
in Λ. The Suzuki lemma gives the dihedral or semidihedral Sylow alternative.

Source: Aschbacher--Smith C.6.1(6b), printed p.164.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]
variable {H M K R : Subgroup G}

theorem cubic_small_core_sylow
    (c : OriginalHypotheses H M K R R) (hK : IsAlternatingBlock K 3)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hsmall : H.pCoreIn 2 = sourceModule K) :
    IsDihedralGroup Λ ∨ IsSemidihedralGroup Λ := by
  let U := sourceModule K
  let : IsElementaryAbelian 2 U := hK.2.1.elementary.map K.subtype
  have hcard : Nat.card U = 4 := RankOneSetup.cubic_module_card hK
  have hU : U ≠ ⊥ := by intro he; simp only [he,card_bot] at hcard; omega
  change H.pCoreIn 2 = U at hsmall
  have hUR : U ≤ R := by
    rw [←hsmall]
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hUΛ : U ≤ Λ := hUR.trans hRΛ.le
  have hHU : H ≤ normalizer (U : Set G) := by
    rw [←hsmall]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hN : Λ ⊓ normalizer (U : Set G) = R := hcontrol U hU hUR hHU
  have hC : R ⊓ centralizer (U : Set G) = U :=
    (original_core_eq_module_centralizer c hK.2.1).trans hsmall
  let V := U.subgroupOf Λ
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hUΛ
  have hV : Nat.card V = 4 := (Nat.card_congr (subgroupOfEquivOfLe hUΛ).toEquiv).trans hcard
  have hp : V ≠ ⊤ := fun he => hRΛ.not_ge ((subgroupOf_eq_top.mp he).trans hUR)
  have hs : centralizer (V : Set Λ) = V := by
    apply le_antisymm _ V.le_centralizer
    intro a ha
    have hac : (a : G) ∈ centralizer (U : Set G) := by
      intro u hu
      exact congrArg Subtype.val (ha ⟨u,hUΛ hu⟩ hu)
    have har : (a : G) ∈ R := hN ▸
      (show (a : G) ∈ Λ ⊓ normalizer (U : Set G) from
        ⟨a.property,Subgroup.centralizer_le_normalizer _ hac⟩)
    change (a : G) ∈ U
    exact hC ▸ (show (a : G) ∈ R ⊓ centralizer (U : Set G) from ⟨har,hac⟩)
  exact dihedral_or_semidihedral_of_selfCentralizing_four hΛ V hV hp hs

end CFSG.Quasithin.ChapterC.Section06
