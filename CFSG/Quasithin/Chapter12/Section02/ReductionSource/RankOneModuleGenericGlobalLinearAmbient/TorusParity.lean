module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.TorusParity
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.AmbientGeneration

/-!
# The original linear Weyl pair and Sylow-intersection criterion

The prepared maximal row supplies endpoint involutions escaping the whole
normalizer overlap. They normalize one marked odd split torus, their product
has odd order, and its cube centralizes that torus. The original involution
centralizer theorem also identifies disjoint Sylows by odd-order products
of their marked central involutions.

These are literal applications to the chosen Chapter12 module, preserving
n>1, field four and both orientations. The Hall-normalizer coset bound and
cube membership in the whole overlap remain required for GlobalExit.
Source: Aschbacher–Smith, F.4.46–49, pp.297–299, applied to 12.2, p.795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

/-- The unchanged chosen-module hypotheses produce the original endpoint
reflections and their common odd split torus, with odd-order product.
The cube centralizes the torus; its membership in the whole overlap remains
the final Hall-coset obligation. -/
theorem rankOne_global_linear_odd_weyl_witness :
    ∃ D₀ : Subgroup G,
      D₀ ≤ ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H) ∧
      Odd (Nat.card D₀) ∧ ∃ s t : G,
      s ∈ normalizer (L : Set G) ∧ t ∈ normalizer (residual H : Set G) ∧
      s ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      t ∉ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      s^2=1 ∧ t^2=1 ∧ s ∈ normalizer (D₀ : Set G) ∧ t ∈ normalizer (D₀ : Set G) ∧
      (s*t)^3 ∈ centralizer (D₀ : Set G) ∧ Odd (orderOf (s*t)) :=
  d.linear_odd_weyl_witness (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax

/-- Source F.4.48's odd-product criterion holds for the original ambient
Sylow and every element outside its full normalizer. -/
theorem rankOne_global_linear_odd_product_iff_disjoint_sylows
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (Global.sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G)) :
    Odd (orderOf (z*(g*z*g⁻¹))) ↔
      Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g) :=
  d.linear_odd_product_iff_disjoint_sylows (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzZ g hg



/-- The actual swapping involution for disjoint original Sylows preserves the
intersection of their full normalizers, as required in F.4.49. -/
theorem rankOne_global_linear_disjoint_sylow_swap
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (Global.sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G))
    (hdis : Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g)) :
    ∃ w : G, orderOf w=2 ∧
      (T : Subgroup G).conjBy w=(T : Subgroup G).conjBy g ∧
      ((T : Subgroup G).conjBy g).conjBy w=(T : Subgroup G) ∧
      w ∈ normalizer ((normalizer (T : Set G) ⊓
        normalizer ((T : Subgroup G).conjBy g : Set G) : Subgroup G) : Set G) :=
  d.linear_disjoint_sylow_swap (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax z hz hzZ g hg hdis

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
