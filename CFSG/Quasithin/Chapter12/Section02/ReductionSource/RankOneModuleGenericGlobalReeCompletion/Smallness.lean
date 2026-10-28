module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.Smallness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeCompletion

/-!
# The original Chapter12 Ree pair under the field-factor order bound

Apply the eight-path count to the actual prepared whole-residual pair.
The resulting octagon uses the original n=2m+1, both compatible comparison
orientations and the full Borel overlap. No cycle or diameter is assumed.
The displayed ambient order bound is still a premise, and octagon geometry
does not yet give the required native Ree GlobalExit. Its discharge and the
ambient group identification remain in the same source family.

Source: Aschbacher–Smith 5.3.2–4, F.4.24,43–44 and the Chapter12 application,
printed pp.659,287,296,795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
open ChapterF.SourceCompletion.GeneralReeFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- Actual Chapter12 application of the source smallness count. The ambient
order bound remains an explicit obligation of the Ree recognition assembly. -/
theorem rankOne_global_ree_completion_small_of_order_bound
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
    (horder : Nat.card G ≤ n * Nat.card (ReeF4.Model m)) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w, c.graph.dist v w ≤ 8) ∧
      (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16) := by
  exact d.ree_completion_small_of_order_bound
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he horder

/-- The literal source comparison |G| ≤ |Mbar| suffices once Mbar has a
faithful action on the complete native model. Both inputs remain explicit;
the proved automorphism bound discharges the intervening field-factor estimate. -/
theorem rankOne_global_ree_completion_small_of_extension_comparison
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
    {E : Type*} [Group E] [Finite E]
    (ρ : E →* MulAut (ReeF4.Model m)) (hρ : Function.Injective ρ)
    (hcomparison : Nat.card G ≤ Nat.card E) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ e : RankTwoAmalgam.Iso
        (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (Global.sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w, c.graph.dist v w ≤ 8) ∧
      (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16) := by
  exact d.ree_completion_small_of_extension_comparison
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he ρ hρ hcomparison

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
