module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Fusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion.ShortCentralizer

/-!
# Original Chapter12 applications of Ree involution fusion

The original chosen-module inputs give the prepared whole-residual pair.
Its literal full-normalizer maps carry extension involution conjugacies to
the ambient group, including conjugacies between elements of the original
Sylow through the whole common-normalizer map. Every ambient involution
has a representative marked by an actual native Ree involution.

The simultaneous constructor preserves both comparison orientations and
the original degree 2m+1=n. These prove the involution specialization of
F.4.30 and the Sylow reduction for F.4.35. Two-class exhaustion, the short-centralizer
bound, order comparison and final GlobalExit remain unproved.
Source: Aschbacher–Smith 5.3.1–3, F.4.30,35,40–43 and 12.2.2,
printed pp.658–659,290–296,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual full-normalizer endpoint maps carry model involution fusion to the original ambient group. -/
theorem rankOne_global_ree_extension_involution_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    {i j : Bool} (x : R.extension.family i) (y : R.extension.family j)
    (hx : orderOf x.val = 2) (hxy : IsConj x.val y.val) :
    IsConj (R.endpointInverse i x) (R.endpointInverse j y) :=
  d.ree_extension_involution_fusion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hp m R x y hx hxy

/-- The literal original common normalizer, including its entire Sylow, inherits the model-to-ambient fusion implication. -/
theorem rankOne_global_ree_middle_involution_fusion
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m)
    (x y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
    (hx : orderOf x.val = 2)
    (hxy : IsConj (R.middleToCarrier x) (R.middleToCarrier y)) :
    IsConj x.val y.val :=
  d.ree_middle_involution_fusion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hp m R x y hx hxy

/-- Both source orientations supply one full marking with endpoint fusion and native representatives for every ambient involution. -/
theorem rankOne_global_ree_full_extension_fusion
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
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse)) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ R : Global.ReeNormalizerMarking L (residual H) (Global.sourceS L H) m,
      (∀ (i j : Bool) (x : R.extension.family i) (y : R.extension.family j),
        orderOf x.val = 2 → IsConj x.val y.val →
          IsConj (R.endpointInverse i x) (R.endpointInverse j y)) ∧
      ∀ x : G, orderOf x = 2 →
        ∃ (y : (normalizer (L : Set G) ⊓ normalizer (residual H : Set G) : Subgroup G))
          (t : ReeF4.Model m),
          y.val ∈ (T : Subgroup G) ∧ orderOf t = 2 ∧ IsConj x y.val ∧
          R.middleToCarrier y = R.extension.baseHom t :=
  d.ree_full_extension_fusion (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
