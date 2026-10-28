module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalReeOvercomponent

/-!
# Full-normalizer actions on the original Chapter12 Ree completion

The actual compatible Ree comparison and the original Preparation give
the source local conditions with right maximality discharged. They now
construct a faithful conjugation action of the full normalizer join on
J = ⟨L,O²(H)⟩. This J is the original perfect residual, is normal in that
join, and has trivial ambient centralizer. The two restricted actions
retain both literal normalizers and their entire overlap, including its
odd Cartans, as their exact image intersection.

The comparison still concerns the original source parabolics. It does not
identify J or the ambient G with a Ree group. Constructing the exhaustive
comparison and proving these completion identifications remain with this
owner; original uniqueness remains in Preparation and retains its producer.
No new action or faithfulness premise is imposed on the Chapter12 setup.

Source: Aschbacher–Smith 5.2.6–8 and 5.3.1–2, printed pp.650–653,658–659;
the Chapter12 application is on p.795 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The actual full-normalizer completion acts faithfully on the original
perfect factor join in the Ree branch. The compatible maps agree on the
whole intersection, without identifying that intersection with a Sylow. -/
theorem rankOne_global_ree_normalizer_completion_action
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
    let K := residual H
    let J := L ⊔ K
    let M := normalizer (L : Set G) ⊔ normalizer (K : Set G)
    Group.IsPerfect J ∧ (J.subgroupOf M).Normal ∧ centralizer (J : Set G) = ⊥ ∧
      ∃ ρ : M →* MulAut J, Function.Injective ρ ∧
        (∀ g x, ((ρ g x : J) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
        (MulAut.conj : J →* MulAut J).range ≤ ρ.range := by
  dsimp only
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  have hc := d.ree_normalizer_local_conditions hi hH hp m he
  have hpL := Chapter1.mem_L_isPerfect hi.local_mem.1.1
  have hres := Global.residual_pair_solvableResidual
    hi.sylow_normalizes hH.1.1.2 hpL hp
  have hpJ : Group.IsPerfect (L ⊔ residual H : Subgroup G) := by
    have ht : Group.IsPerfect
        ((solvableResidual (L ⊔ H : Subgroup G)).map (L ⊔ H).subtype) :=
      Group.IsPerfect.map _
    rwa [hres] at ht
  exact ⟨hpJ,normal_subgroupOf_of_le_normalizer (Global.normalizer_pair_normalizes hc),
    Global.normalizer_pair_centralizer_eq_bot hc,Global.normalizer_pair_inner_action hc⟩

/-- Both actual full normalizers have faithful compatible actions, with the
whole overlap as their exact image intersection. This is the group-action
part of 5.3.2; identification of the perfect completion remains separate. -/
theorem rankOne_global_ree_normalizer_compatible_actions
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
    let K := residual H
    let J := L ⊔ K
    ∃ (l : normalizer (L : Set G) →* MulAut J)
      (r : normalizer (K : Set G) →* MulAut J)
      (b : (normalizer (L : Set G) ⊓ normalizer (K : Set G) : Subgroup G) →* MulAut J),
      Function.Injective l ∧ Function.Injective r ∧ Function.Injective b ∧
      (∀ g x, ((l g x : J) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
      (∀ g x, ((r g x : J) : G) = (g : G) * (x : G) * (g : G)⁻¹) ∧
      (∀ x, l (inclusion inf_le_left x) = b x) ∧
      (∀ x, r (inclusion inf_le_right x) = b x) ∧
      l.range ⊓ r.range = b.range ∧
      (MulAut.conj : J →* MulAut J).range ≤ l.range ⊔ r.range := by
  exact Global.normalizer_pair_compatible_actions
    (d.ree_normalizer_local_conditions
      (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m he)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
