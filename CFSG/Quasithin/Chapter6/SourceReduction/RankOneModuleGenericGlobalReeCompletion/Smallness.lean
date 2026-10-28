module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.Smallness
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Automorphisms

/-!
# Smallness of the original prepared Ree pair from the ambient order bound

The original compatible comparison gives the marked completion on L ∨ O²(H).
Its order is bounded by the ambient order. Thus the source comparison
|G| ≤ n|ReeF4.Model m|, with the original n=2m+1, forces an actual
sixteen-cycle and diameter eight. The strict counting inequality uses n<2^n,
so it covers q=8 and every larger positive parameter. Both local maps and
the whole original Borel overlap are retained.

This discharges the geometric smallness step conditional on the stated
order bound. The compatible native normalizer extension, ambient order bound,
and group recognition remain with this source family; none is asserted here.
Source: Aschbacher–Smith 5.3.2–4 and F.4.24,43–44,
printed pp.659,287,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion.GeneralReeFour
variable {G : Type*} [Group G] [Finite G]

/-- The original prepared whole-residual completion is small once the ambient
order comparison with a field-factor extension is supplied. -/
theorem Preparation.ree_completion_small_of_order_bound
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    (horder : Nat.card G ≤ n * Nat.card (ReeF4.Model m)) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w, c.graph.dist v w ≤ 8) ∧
      (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16) := by
  obtain ⟨hn,hm,_,_,e,c,hl,hr,hb,hc,hconn,_,_,_⟩ :=
    d.ree_completion_geometry h hH hp m he
  have hq : n < 2^(2*m+1) := by rw [hn]; exact Nat.lt_two_pow_self
  have hj : Nat.card (L ⊔ residual H : Subgroup G) ≤ n * Nat.card (ReeF4.Model m) :=
    (Nat.card_le_card_of_injective (L ⊔ residual H).subtype
      (L ⊔ residual H).subtype_injective).trans horder
  exact ⟨hn,hm,e,c,hl,hr,hb,hc,hconn,c.octagon_metric_of_order_bound hm hc hq hj⟩

/-- The literal source comparison |G| ≤ |Mbar| suffices once Mbar has a
faithful action on the complete native model. Both inputs remain explicit;
the proved automorphism bound discharges the intervening field-factor estimate. -/
theorem Preparation.ree_completion_small_of_extension_comparison
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
    {E : Type*} [Group E] [Finite E]
    (ρ : E →* MulAut (ReeF4.Model m)) (hρ : Function.Injective ρ)
    (hcomparison : Nat.card G ≤ Nat.card E) :
    2*m+1 = n ∧ 0 < m ∧
    ∃ e : RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse,
    ∃ c : Completion m (L ⊔ residual H : Subgroup G),
      (∀ x, (c.left x : G) = (e.left.symm x : G)) ∧
      (∀ x, (c.right x : G) = (e.right.symm x : G)) ∧
      c.middle.range = (ChapterF.Source.commonBorel ![L,residual H] (sourceS L H)).subgroupOf
        (L ⊔ residual H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      c.graph.Connected ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 16 ≤ p.length) ∧
      (∀ v w, c.graph.dist v w ≤ 8) ∧
      (∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=16) := by
  have hm : 0 < m := (d.ree_completion_geometry h hH hp m he).2.1
  have hn : 2*m+1=n := (d.ree_completion_geometry h hH hp m he).1
  have horder := hcomparison.trans (ReeF4.SourceCompletion.card_extension_le hm ρ hρ)
  rw [hn] at horder
  exact d.ree_completion_small_of_order_bound h hH hp m he horder

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
