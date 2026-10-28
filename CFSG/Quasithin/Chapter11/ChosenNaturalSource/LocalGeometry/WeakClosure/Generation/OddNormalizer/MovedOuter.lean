module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.MovedCases
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremB.Basic
public import Theory.GroupTheory.PerfectNormalizerInner.SimpleSection
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel

/-!
# Inner placement or the actual natural simple section in Out(K)

The original odd fixed residual maps onto the simple central quotient of
L/O₂(L), with solvable kernel. Its action on the selected component is
therefore inner unless that same simple group occurs as a section of Out(K).
The completed outer calculations exclude all Theorem C, alternating, and
odd PSL₂ models from the latter alternative. In the inner alternative,
residual uniqueness places the original V and residual in a normal component.
Its literal central image retains the full covering quotient and has two-rank
at least six and order divisible by 2¹².

Source applies this dichotomy to the original Hall kernel. The remaining
model exclusions belong to qt-d-1222-natural-odd-kernel-normalizer; final
11.2.1 assembly belongs to qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The outer obstruction is a section of the actual component's outer group,
with the simple quotient of the original full cover as its target. -/
theorem moved_component_inner_or_outer_section {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) :
    (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G))) ∨
    ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f := by
  classical
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  by_cases ho : ∃ U : Subgroup (MulAut.Outer K),
      ∃ f : U →* coreCentralQuotient L, Function.Surjective f
  · exact Or.inr ho
  apply Or.inl
  let F := oddActorResidual L A
  let N := normalizer (A : Set G)
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let u : F.subgroupOf N ≃* F := subgroupOfEquivOfLe hFN
  obtain ⟨e,_⟩ := actor_cover_quotient D S hA hodd
  let ec : ((F.subgroupOf N) ⧸ pCore 2 (F.subgroupOf N)) ≃* (L ⧸ pCore 2 L) :=
    (QuotientGroup.congr _ _ u (pCore_map_iso 2 u)).trans e
  let ez := QuotientGroup.congr _ _ ec (FixedElementary.map_center ec)
  let q := QuotientGroup.mk' (pCore 2 (F.subgroupOf N))
  let z := QuotientGroup.mk' (center ((F.subgroupOf N) ⧸ pCore 2 (F.subgroupOf N)))
  let f : F.subgroupOf N →* coreCentralQuotient L := ez.toMonoidHom.comp (z.comp q)
  have hf : Function.Surjective f := ez.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hk : f.ker = centralPreimage (pCore 2 (F.subgroupOf N)) := by
    ext x
    change ez (z (q x)) = 1 ↔ q x ∈ center ((F.subgroupOf N) ⧸ pCore 2 (F.subgroupOf N))
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (q x)
  let : Group.IsSolvable f.ker := hk ▸ centralPreimage_pCore_isSolvable 2
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := u.symm.toMonoidHom) u.symm.surjective
  obtain ⟨_,hFK,_⟩ := chosen_oddNormalizer_component_normalization
    S.source.toHypothesis1221 D A (hA.trans inf_le_left) (actor_commutator D S hA)
    hodd (hA.trans inf_le_right) K hK
  exact perfect_le_sup_centralizer_of_no_simple_outer_section K (F.subgroupOf N)
    f hf (fun U g hg => ho ⟨U,g,hg⟩) hFK

/-- Inner action places the original module and full residual, for every B-model.
No equality |V| = 64 and no center-free cover is assumed. -/
theorem moved_component_placement_of_inner {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (hi : (oddActorResidual L A).subgroupOf (normalizer (A : Set G)) ≤
      K ⊔ centralizer (K : Set (normalizer (A : Set G)))) :
    K.Normal ∧ V ≤ K.map (normalizer (A : Set G)).subtype ∧
      oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
      centralizer (K : Set (normalizer (A : Set G))) = pPrimeCore 2 (normalizer (A : Set G)) ∧
      NaturalCoverImage D (K ⧸ center K) ∧
      6 ≤ primeRank 2 (K ⧸ center K) ∧ 2 ^ 12 ∣ Nat.card (K ⧸ center K) := by
  have hv := chosen_oddNormalizer_module_le_of_component_inner_action
    S.source.toHypothesis1221 D A (hA.trans inf_le_left) (actor_commutator D S hA)
    hodd (hA.trans inf_le_right) hu K houtK hi
  have ho := chosen_oddNormalizer_component_centralizer_odd S.source.toHypothesis1221 D
    (centralizer_eq_core D S).le A (hA.trans inf_le_left) (actor_commutator D S hA)
    hodd (hA.trans inf_le_right) hu hout K hK houtK hv
  let N := normalizer (A : Set G)
  let F := oddActorResidual L A
  have hFN : F ≤ N := ((oddActorResidual_le L A).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  let : Group.IsPerfect F := oddActorResidual_isPerfect L A
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFN).symm.surjective
  have hf : F ≤ K.map N.subtype := by
    have hh := map_mono (f := N.subtype)
      (hK.perfect_actor_le_of_odd_centralizer ho (F.subgroupOf N) hi)
    rwa [map_subgroupOf_eq_of_le hFN] at hh
  have himage := placed_residual_natural_cover_image D S hA hodd K hf
  exact ⟨hK.normal_of_odd_centralizer ho,hv,hf,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho,himage,
    himage.twoRank_ge_six D S,himage.two_power_dvd D S⟩

/-- The completed outer-solvability rows cannot carry the actual simple section. -/
theorem moved_outer_section_exclusions {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) :
    ¬ ChapterA.Section02.IsTheoremCModel (K ⧸ center K) ∧
      (∀ n : ℕ, ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin n))) ∧
      (∀ q : ℕ, Odd q → ¬ ClassicalGroup.IsPSL (K ⧸ center K) 2 q) := by
  let := S.source.toHypothesis1221.quasisimple
  let : IsSimpleGroup (coreCentralQuotient L) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient L) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center (L ⧸ pCore 2 L))) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsPerfect (K ⧸ center K) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  have hna : ¬ IsMulCommutative (K ⧸ center K) := Group.IsPerfect.not_isMulCommutative _
  have hns : ¬ Group.IsSolvable (MulAut.Outer (K ⧸ center K)) := by
    intro hs
    let := hs
    let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
      (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
    obtain ⟨U,f,hf⟩ := ho
    exact Group.IsPerfect.not_isSolvable (coreCentralQuotient L)
      (Group.isSolvable_of_surjective hf)
  exact ⟨fun hc => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.of_theoremC hna hc),
    fun n hn => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.alternating hna hn),
    fun q hq hm => hns (ChapterA.Section03.SourceComponents.TheoremBOuter.linear_two_odd hna hq hm)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
