module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ProjectionOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.Reduction
public import CFSG.Quasithin.Chapter4.Section04.OddActorComponents.NormalSource

/-!
# Normal placement of the actual moved component in the shared Theorem C rows

For the literal N_G(A), the perfect covering residual acts by inner
automorphisms on each of the completed Theorem C models. Uniqueness of its
maximal two-local overgroup kills the centralizer projection of the original V.
Faithfulness of the actual natural action then forces the component centralizer
to be odd, making the component normal and containing the entire residual.
No equality |V| = 64 is assumed; fixed vectors and central covers are retained.

The endpoint uses this result in the moved-component alternative. The remaining
full Theorem B rows and final local exclusions stay with the odd-normalizer owner.
Source: Aschbacher--Smith 4.4.10--11, printed p.621.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The selected component is normal and contains the original module and residual
whenever its literal central quotient lies on the completed C-model list. -/
theorem moved_component_normal_of_theoremC {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hmodel : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) := by
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC
      (Group.IsPerfect.not_isMulCommutative _) hmodel
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  obtain ⟨_,hFK,_⟩ := chosen_oddNormalizer_component_normalization S.source.toHypothesis1221 D
    A (hA.trans inf_le_left) (actor_commutator D S hA) hodd (hA.trans inf_le_right) K hK
  have hi := perfect_le_sup_centralizer_of_solvable_outer K (F.subgroupOf N) hFK
  have hv := chosen_oddNormalizer_module_le_of_component_inner_action S.source.toHypothesis1221 D
    A (hA.trans inf_le_left) (actor_commutator D S hA) hodd (hA.trans inf_le_right) hu K houtK hi
  have ho := chosen_oddNormalizer_component_centralizer_odd S.source.toHypothesis1221 D
    (centralizer_eq_core D S).le A (hA.trans inf_le_left) (actor_commutator D S hA)
    hodd (hA.trans inf_le_right) hu hout K hK houtK hv
  have hf : F ≤ K.map N.subtype := by
    have hh := map_mono (f := N.subtype) (hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hi)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  exact ⟨hK.normal_of_odd_centralizer ho,hv,hf,hK.centralizer_eq_oddCore_of_odd_centralizer ho⟩

/-- Once the actual residual is placed in the selected component, its central
projection again retains both original natural factors. Odd covering centers
are harmless: faithfulness forces their intersection with the residual into
its two-core, rather than silently discarding the full SL₃ center. -/
theorem placed_residual_product_card_dvd {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hf : oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype) :
    Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) ∣ Nat.card (K ⧸ center K) := by
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFL : F ≤ L := (oddActorResidual_le L A).trans inf_le_left
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFK : F.subgroupOf N ≤ K := by
    intro x hx
    obtain ⟨k,hk,hkx⟩ := hf hx
    exact (Subtype.ext hkx : k = x) ▸ hk
  let ef : (F.subgroupOf N).subgroupOf K ≃* F :=
    (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  let j : F →* K := ((F.subgroupOf N).subgroupOf K).subtype.comp ef.symm.toMonoidHom
  have hj : Function.Injective j :=
    ((F.subgroupOf N).subgroupOf K).subtype_injective.comp ef.symm.injective
  let f := (QuotientGroup.mk' (center K)).comp j
  have hcentral : f.ker ≤ center F := by
    intro b hb
    apply mem_center_iff.mpr
    intro c
    apply hj
    simpa only [map_mul] using
      (mem_center_iff.mp ((QuotientGroup.eq_one_iff (j b)).mp hb)) (j c)
  obtain ⟨hc,_,hVcore,_⟩ := actor_cover D S hA hodd
  have hVF : V ≤ F := hVcore.trans (pCoreIn_le 2 F)
  have hker : f.ker ≤ (L.pCoreIn 2).comap F.subtype := by
    intro b hb
    apply (centralizer_eq_core D S).le
    refine ⟨hFL b.property,?_⟩
    intro v hv
    exact congrArg Subtype.val ((mem_center_iff.mp (hcentral hb)) ⟨v,hVF hv⟩)
  have hk : IsPGroup 2 f.ker := ((isPGroup_pCoreIn 2 L).comap_subtype).to_le hker
  exact (natural_cover_projection_order D S hFL hc hVcore f hk hcentral).trans
    f.range.card_subgroup_dvd_card

/-- Every moved C-model component retains the same twelve binary factors.
This is a consequence of proved placement, with no |V| = 64 premise. -/
theorem moved_component_two_power_dvd {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G))) (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hmodel : ChapterA.Section02.IsTheoremCModel (K ⧸ center K)) :
    2 ^ 12 ∣ Nat.card (K ⧸ center K) := by
  have hf := (moved_component_normal_of_theoremC D S hA hodd hu hout K hK houtK hmodel).2.2.1
  have hd := placed_residual_product_card_dvd D S hA hodd K hf
  obtain ⟨hv,hq⟩ := natural_two_parts D S
  exact (show 2 ^ 12 ∣ Nat.card D.chosenCentralQuotient * Nat.card (L ⧸ pCore 2 L) from
    by simpa only [show (64 * 64 : ℕ) = 2 ^ 12 by decide] using Nat.mul_dvd_mul hv hq).trans hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
