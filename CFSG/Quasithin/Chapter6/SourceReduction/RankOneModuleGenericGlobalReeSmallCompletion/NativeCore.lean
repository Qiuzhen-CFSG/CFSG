module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeSmallCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Simple
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.Cartan
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.EquivTransport

/-!
# Native-amalgam reduction for the original full normalizer completion

The checked full-extension census puts the join of the original normalizers
equal to G. Inside their completion the marked native images generate a normal
subgroup of native order. Ambient simplicity makes that subgroup all of G,
so the original source inputs give a faithful native-amalgam completion in G
of exactly the native group order. Its positive and Cartan images retain the
proved fixed-point and normalizer calculations.

A native group isomorphism and GlobalExit still require group recognition.
The compatible extension and full ambient order bound remain the same earlier
source premises. Source: Aschbacher–Smith 5.3.1–4 and F.4.17,24, pp.658–659,283,287.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeExtension
open ChapterF.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- Simplicity reduces the actual full-normalizer completion to the native
amalgam with exact native order and the literal marked Cartan calculations. -/
theorem Preparation.ree_full_normalizers_native_completion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (E : SourceExtension m)
    (hext : Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (UnitaryNonbinary.Generated.amalgam (normalizer (L : Set G)) (normalizer (residual H : Set G))) E.amalgam.reverse))
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    2*m+1 = n ∧ 0 < m ∧ Nat.card G = Nat.card (ReeF4.Model m) ∧
      ∃ c : GeneralReeFour.Completion m G,
        c.left.range ⊓ c.right.range = c.middle.range ∧
        ((ReeF4.Parabolics.unipotent m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle ⊓
          centralizer (((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle : Set G) = ⊥ ∧
        c.middle.range ⊓ normalizer
          (((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle : Set G) =
          ((ReeF4.Parabolics.fixedTorus m).subgroupOf (ReeF4.Parabolics.borel m)).map c.middle := by
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨hn,hm,htop,_,c,hc,_⟩ :=
    d.ree_full_normalizers_small_completion h hH hp m he E hext horder
  let e : (normalizer (L : Set G) ⊔ normalizer (residual H : Set G) : Subgroup G) ≃* G :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  let cG := c.mapEquiv e
  have hcG := c.mapEquiv_overlap e hc
  let r := nativeAmbientCompletion E cG hm hcG horder
  refine ⟨hn,hm,simple_completion_order_eq_native E cG hm hcG horder,r,
    nativeAmbientCompletion_overlap E cG hm hcG horder,?_,?_⟩
  · exact ReeF4.SmallCompletion.mapped_unipotent_inf_centralizer_fixedTorus hm
      r.middle r.middle_injective
  · exact ReeF4.SmallCompletion.mapped_borel_inf_normalizer_fixedTorus hm
      r.middle r.middle_injective

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
