module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.ShortAmbient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.ShortCentralizer

/-!
# Ambient short-centralizer containment for the original Chapter12 Ree row

Native exhaustion and one-way full-left-endpoint fusion suffice to choose a
short representative whose original T-centralizer is Sylow in its ambient
centralizer. The same full-normalizer extension, radical and core placement,
whole-overlap marking, entire extension centralizer, and nonfusion remain
literal. The marked extension Sylow centralizer is obtained simultaneously.

This discharges the extremal-selection step of F.4.40 in the original 12.2.2
row. It also gives the commuting-class incidence comparison and unique
fixed cosets for original long involutions, together with a faithful native
PSL₂ action on the same selected marker's long-root plane. Full endpoint
invariance and I.8.5 now give ambient F.4.42 containment and the entire
centralizer equivalence, retaining its actual endpoint-map equality.
Source: Aschbacher–Smith,
printed pp.294–295,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ReeF4 ReeF4.Parabolics ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual chosen-module inputs select an extremal short marker in the
same supplied extension, under only the indicated earlier-source premises. -/
theorem rankOne_global_ree_short_extremal_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hfusion : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (R.leftToCarrier x) (R.leftToCarrier y)) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      (∃ Q : Sylow 2 (centralizer ({v} : Set (normalizer (L : Set G)))),
        (Q : Subgroup (centralizer ({v} : Set (normalizer (L : Set G))))) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G))).subgroupOf
            (centralizer ({v} : Set (normalizer (L : Set G))))) ∧
      (∃ Q : Sylow 2 (centralizer ({v.val} : Set G)),
        (Q : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier ∧
        R.extension.baseHom t ∈ S ∧
        ∃ Q : Sylow 2 (centralizer ({R.extension.baseHom t} : Set R.extension.carrier)),
          (Q : Subgroup (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) =
            (S : Subgroup R.extension.carrier).subgroupOf
              (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  exact d.ree_short_extremal_comparison
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he R hexhaust hfusion

/-- The original Chapter12 inputs supply the same extremal marker, the
unique fixed cosets of all original long involutions, and a faithful native
PSL₂ action on its literal long-root plane. -/
theorem rankOne_global_ree_short_incidence_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hleft : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (R.leftToCarrier x) (R.leftToCarrier y))
    (hcross : ∀ x : normalizer (L : Set G),
      ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (R.leftToCarrier x) (R.rightToCarrier y))) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      (∃ R : Sylow 2 (centralizer ({v.val} : Set G)),
        (R : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier ∧
        R.extension.baseHom t ∈ S ∧
        ∃ Q : Sylow 2 (centralizer ({R.extension.baseHom t} : Set R.extension.carrier)),
          (Q : Subgroup (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) =
            (S : Subgroup R.extension.carrier).subgroupOf
              (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) ∧
      (∀ z : center (residual H), orderOf z = 2 →
        ∀ a : centralizer ({v.val} : Set G), IsConj z.val.val a.val →
          ∃! q : centralizer ({v.val} : Set G) ⧸
            (normalizer (L : Set G)).subgroupOf (centralizer ({v.val} : Set G)), a • q = q) ∧
      (ReeF4.ElementaryTwoBound.Replacement.V m ≤ centralizer ({t} : Set (Model m))) ∧
      ∃ f : LargeLocalSeeds.LinearQuotient m →* centralizer ({t} : Set (Model m)),
        ∃ ρ : LargeLocalSeeds.LinearQuotient m →*
            MulAut (ReeF4.ElementaryTwoBound.Replacement.V m),
          Function.Injective f ∧ Function.Injective ρ ∧
          ∀ x w, (ρ x w : Model m) = (f x).val * w.val * (f x).val⁻¹ := by
  exact d.ree_short_incidence_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he R hexhaust hleft hcross

/-- F.4.42 on the original Chapter12 chosen-module row, for every positive
Ree parameter including q = 8. The same extremal marker retains its literal
full Sylow, core and extension markings. Its entire ambient centralizer lies
in the original left normalizer, and the centralizer equivalence is the
restriction of that normalizer marking. Only earlier native exhaustion and
full-endpoint fusion remain explicit for the ambient assembly owner. -/
theorem rankOne_global_ree_short_ambient_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse))
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (hexhaust : ∀ x : Model m, orderOf x = 2 →
      IsLongRootInvolution x ∨ IsShortRootInvolution x)
    (hleft : ∀ x y : normalizer (L : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 → IsConj x.val y.val →
        IsConj (R.leftToCarrier x) (R.leftToCarrier y))
    (hcross : ∀ x : normalizer (L : Set G),
      ∀ y : normalizer (residual H : Set G),
      orderOf x.val = 2 → orderOf y.val = 2 →
        (IsConj x.val y.val ↔ IsConj (R.leftToCarrier x) (R.rightToCarrier y))) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ v.val ∈ T ∧ orderOf v.val = 2 ∧
      R.leftToCarrier v = R.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        R.leftToCarrier = centralizer ({R.extension.baseHom t} : Set R.extension.carrier) ∧
      (∃ Q : Sylow 2 (centralizer ({v.val} : Set G)),
        (Q : Subgroup (centralizer ({v.val} : Set G))) =
          (T : Subgroup G).subgroupOf (centralizer ({v.val} : Set G))) ∧
      (∃ S : Sylow 2 R.extension.carrier,
        (S : Subgroup R.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map R.middleToCarrier ∧
        R.extension.baseHom t ∈ S ∧
        ∃ Q : Sylow 2 (centralizer ({R.extension.baseHom t} : Set R.extension.carrier)),
          (Q : Subgroup (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) =
            (S : Subgroup R.extension.carrier).subgroupOf
              (centralizer ({R.extension.baseHom t} : Set R.extension.carrier))) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      (∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val) ∧
      ∃ hC : centralizer ({v.val} : Set G) ≤ normalizer (L : Set G),
        ∃ e : centralizer ({v.val} : Set G) ≃*
            centralizer ({R.extension.baseHom t} : Set R.extension.carrier),
          ∀ x, (e x).val = R.leftToCarrier ⟨x.val,hC x.property⟩ := by
  exact d.ree_short_ambient_comparison
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he R hexhaust hleft hcross

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
