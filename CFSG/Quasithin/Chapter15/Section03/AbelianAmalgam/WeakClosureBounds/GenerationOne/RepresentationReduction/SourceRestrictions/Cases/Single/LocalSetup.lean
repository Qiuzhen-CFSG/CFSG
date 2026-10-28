module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CentralComparison
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications

/-!
# The actual local action for the single-component deduction

This is the specialization contract for the generic section and orbit lemmas:
D=H/O₂(H), V=U/Z, U=⟨ZS^H⟩, and the chosen T-homogeneous Irr⁺ section for K.
It retains the earlier E.2.2 reduction and the numerical hypotheses of 15.3.65.
No representation classification or model exclusion is included in the input.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.65,
printed pp.1151--1152; E.2.2, pp.215--216; F.9.18, pp.325--326.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The local specialization contract for the generic section development.
These are earlier source inputs, not an assertion of the desired module cases.
`source.exponent_gt_one` retains f>1; the quotient action retains faithfulness
and its formula on every conjugation representative. -/
structure LocalInput (𝒦 : GroupClass.{u}) (H M K T Z ZS : Subgroup G) (f : ℕ)
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
    (I : Submodule (ZMod 2)
      (Additive ((conjugateSpanBy ZS H) ⧸ Z.subgroupOf (conjugateSpanBy ZS H)))) : Prop where
  local_sqtk : IsSQTK 𝒦 H
  source : BorelReduction.SourceCases.Reduction 𝒦 H M K T f
  single : conjugateSpanBy K T = K
  sylow : ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T
  odd : Odd f
  noThree : ¬ 3 ∣ Nat.card (M ⊓ H : Subgroup G)
  irrPlusWith : IsIrrPlusWith a.representation (actorImage H K) (actorImage H T) I
  quadratic_bound : quadraticRatio a.representation ≤ 2

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single
