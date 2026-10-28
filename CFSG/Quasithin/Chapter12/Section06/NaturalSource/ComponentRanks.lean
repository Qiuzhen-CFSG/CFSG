module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentSuzuki
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The original rank-two Sylow action and exceptional covers

Restrict the constructed KL₁V action to each original Sylow three-subgroup
of L₁. Its image under H → H/O₂(H) remains faithful. If the selected
component has three-rank two, rank saturation places every cubic in its
centralizer inside the component. A trivial component center therefore
makes the restricted action injective.

The genuine A.3.6 catalogue leaves only simple components or the listed
central triple covers: SL₃/SU₃, A₆, A₇ and M₂₂. Quasisimplicity excludes
the alternatives with F* = F. The final original-source constructor retains
condition (*) on the same selected K and the same action, and supplies
rank one or the rank-two faithful-action/cover alternatives.

The use of condition (*) to eliminate the classical and A₆ covers, the
A₇/M₂₂ exclusions, the faithful rank-two exclusion, the rank-one module
argument and Lemma 12.6.26 remain to be proved.
Source: Aschbacher--Smith, proof of 12.6.26, printed pp.832--833.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking
variable {G : Type*} [Group G] {E : Setup G} {H : Subgroup G}
  {c : E.SelectedComponent H} (a : c.ActionMarking)
/-- Restrict the actual KL₁V action to the original Sylow three-subgroup of L₁. -/
noncomputable def residualSylowAction (P : Sylow 3 E.L₁) : P →* MulAut (star H c.K) :=
  a.action.comp ((inclusion (show E.L₁ ≤ c.localActor from le_sup_right.trans le_sup_left)).comp
    (P : Subgroup E.L₁).subtype)
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup.SelectedComponent.ActionMarking

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- Rank saturation and the literal two-core quotient make the original Sylow action faithful when K-star is centerless. -/
theorem SourceHypothesis.original_rank_two_centerless_sylow_faithful
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hr : primeRank 3 c.K = 2)
    (hc : center (Nonabelian.Setup.star H c.K) = ⊥)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Function.Injective (a.residualSylowAction P) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let j : P →* c.localActor := (inclusion (show E.L₁ ≤ c.localActor from
    le_sup_right.trans le_sup_left)).comp (P : Subgroup E.L₁).subtype
  let i := (inclusion a.local_le).comp j
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  have hq := (S.original_point_sylow_star D hZ z hz hTz hH P).2.2
  let := (S.original_point_residual_sylow D hZ z hz hTz P).1
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  have hxker : j x ∈ a.action.ker := hx
  rw [a.kernel] at hxker
  have htC : q (i x) ∈ centralizer (B : Set (Nonabelian.Setup.Hstar H)) := hxker
  have hx3 : x ^ 3 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.val x.property)
  have ht3 : q (i x) ^ 3 = 1 := by
    rw [←map_pow,←map_pow,hx3,map_one,map_one]
  have hrB : primeRank 3 B = 2 := c.three_rank_eq_star.symm.trans hr
  have htB : q (i x) ∈ B := B.mem_of_prime_pow_eq_one_of_centralizes_rank_two
    (S.original_star_three_rank D hZ z hz hH) hrB ht3 htC
  have htZ : (⟨q (i x),htB⟩ : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (htC b.val b.property)
  have ht1 : q (i x) = 1 := by
    have htZ' : (⟨q (i x),htB⟩ : B) ∈ (⊥ : Subgroup B) := by
      rw [←hc]
      exact htZ
    exact congrArg (fun b : B => b.val) (mem_bot.mp htZ')
  have hxA : i x ∈ A.subgroupOf H := mem_map_of_mem E.L₁.subtype x.property
  have he : (⟨i x,hxA⟩ : A.subgroupOf H) = 1 := hq (by
    change q (i x) = q 1
    simpa only [map_one] using ht1)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun y : A.subgroupOf H => y.val.val) he

/-- The ordinary selected component is simple or one of the actual central triple covers in A.3.6. -/
theorem SourceHypothesis.original_selectedComponent_simple_or_cover
    (hz : z ≠ 1) {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    IsSimpleGroup (Nonabelian.Setup.star H c.K) ∨
      (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
        Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)) := by
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  have hF : generalizedFitting B ≠ fittingSubgroup B := by
    intro he
    have htop : fittingSubgroup B = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let hs : Group.IsSolvable (⊤ : Subgroup B) := htop ▸ inferInstanceAs (Group.IsSolvable (fittingSubgroup B))
    exact Group.IsPerfect.not_isSolvable B (Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom) topEquiv.surjective)
  have hc := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) _
    (S.original_star_sqtk D hZ z hz hH) (pCore_quotient_pCore_eq_bot 2) _ c.component.isCComponent
  cases hc.1 with
  | simple _ hs _ => exact Or.inl hs
  | cover _ hcenter hm => exact Or.inr ⟨hcenter,hm⟩
  | natural hh => exact (hF hh.1).elim
  | nilpotent hh => exact (hF hh.1).elim

/-- The first rank-two source split preserves the original P and its literal action on K-star. -/
theorem SourceHypothesis.original_rank_two_sylow_faithful_or_cover
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hr : primeRank 3 c.K = 2) (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Function.Injective (a.residualSylowAction P) ∨
      (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
        Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)) := by
  rcases S.original_selectedComponent_simple_or_cover D hZ z hz hH c with hs|hc
  · left
    let := hs
    let := c.component.2
    apply S.original_rank_two_centerless_sylow_faithful D hZ z hz hTz hH c a hr
    rcases (inferInstance : (center (Nonabelian.Setup.star H c.K)).Normal).eq_bot_or_eq_top with h|h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim
  · exact Or.inr hc
/-- Select the actual K and action with condition (*) and the source three-rank alternatives, retaining all earlier geometry. -/
theorem SourceHypothesis.original_selectedComponent_rank_cases
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H, ∃ a : c.ActionMarking,
      let A := (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let U := ((V.subgroupOf c.localActor).map a.action).subgroupOf a.action.range
      let C := centralizer (U : Set a.action.range)
      (Nat.card U = 2 ∧ 3 ∣ Nat.card A ∧
        A.subgroupOf C ≤ (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) ∧
        ∃ R : Sylow 2 a.action.range, U ≤ (R : Subgroup a.action.range) ∧
          U ≤ centralizer (R : Set a.action.range)) ∧
      (primeRank 3 c.K = 1 ∨ (primeRank 3 c.K = 2 ∧
        ∀ P : Sylow 3 (D.fullSetup hZ T z).L₁,
          Function.Injective (a.residualSylowAction P) ∨
            (Nonempty (center (Nonabelian.Setup.star H c.K) ≃* Multiplicative (ZMod 3)) ∧
              Chapter1.Section02.LocalModels.ThreeCoverModel (Nonabelian.Setup.star H c.K)))) := by
  obtain ⟨c,a,hc⟩ := S.original_selectedComponent_with_condition D hZ z hz hTV hTz hbound hns hH hn
  refine ⟨c,a,hc,?_⟩
  rcases S.original_selectedComponent_three_rank D hZ z hz hTV hTz hbound hns hH hn c with hr|hr
  · exact Or.inl hr
  · exact Or.inr ⟨hr,fun P =>
      S.original_rank_two_sylow_faithful_or_cover D hZ z hz hTz hH c a hr P⟩

end CFSG.Quasithin.Chapter12.Section06
