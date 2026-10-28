module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalComponent
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerThree
public import Theory.Representation.BinaryOffender.QuadraticHomogeneousOrbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SeedCubic

/-!
# Suzuki moved minimality and the remaining centralizing actor

An elementary starred actor moving the original Suzuki component has an
invariant Irr+ member, since Suzuki outer automorphisms have odd order.
The Suzuki endpoint rules out strict ratio descent. The fixed-space
supplement then makes that member the whole moved module, proving
L-minimality without assuming a constituent or a faithful quotient actor.

If every starred actor centralizes the component, D.3.9 supplies moved
support in the exact quotient-action kernel. Its three-core alternative
contradicts the fixed-space plane argument. Both normalized and exchanged
Suzuki support are excluded, so the remaining genuine component has order
divisible by three. The last theorem applies this dichotomy to the literal
Hall subgroup. Excluding that component support and the nonseparated
binary SL2 seed remains necessary for final source assembly.

Source: Aschbacher--Smith D.2.7, D.3.8--9, 10.1.1 and 10.2.3,
printed pp.180,199--201,741,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02

/-- A starred actor moving a normal Suzuki component forces its restriction
on the original space to be irreducible. -/
theorem suzuki_irreducible_of_moving_starred_actor
    {J V : Type*} [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J V) (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (S : Subgroup J) [S.Normal] [IsQuasisimple S]
    (hS : IsSQTK KnownSimple.IsKnownSimple S)
    (m : ℕ) (hm : 0 < m) (e : S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup J) (hA : A ∈ ChapterD.QhatStar ρ)
    (hmove : ¬ A ≤ centralizer (S : Set J)) : IsIrreducible (ρ.comp S.subtype) := by
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup S := e.isSimpleGroup
  have hSn : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf hi S hSn
  have hfixed := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi S hSn
  have hnormal : A ≤ normalizer (S : Set J) := by rw [normalizer_eq_top]; exact le_top
  obtain ⟨I,hI,hAI⟩ := ChosenSource325.exists_invariant_irrPlus_of_suzuki ρ hf S A
    hSn hA.1.2.1.2 hnormal hm e
  have hgen : ⁅S,A⁆ = S := IsComponent.commutator_eq_self_of_normalizes
    (show IsComponent J S from ⟨(inferInstance : S.Normal).isSubnormal,inferInstance⟩)
    hnormal (by
      intro he
      exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)))
  have hnot : ¬ I ≤ fixedSpace ρ A := by
    intro hh
    have hz := le_fixedSpace_commutator_of_invariant ρ hI.choose hh
    rw [hgen] at hz
    exact hI.not_le_fixedSpace ρ hz
  have hItop : I = ⊤ := by
    rcases (ChapterD.QhatStar.restriction_alternatives ρ hA I hAI hnot).2.2 with hd | ⟨_,hs⟩
    · have hb := Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.SuzukiSupport.restricted_actor_ratio_ge_two
        ρ hS hI hAI hnormal hA.1.2.1.2 hm e hd.1
      exact (not_lt_of_ge hb (hd.2.trans_le hA.1.1)).elim
    · exact (hI.eq_moved_of_fixed_span ρ hAI hgen hs).trans hfull
  exact component_irreducible_of_top_isIrrPlus ρ S (hItop ▸ hI) hfixed

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance suzukiMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance suzukiMovedFiniteDimensional : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite

/-- Component irreducibility in the faithful moved image gives literal
L-minimality, without changing the module or quotient map. -/
theorem movedMinimal_of_image_component_irreducible
    (hi : IsIrreducible ((imageRepresentation (movedStabilizerAction D)).comp
      (movedStabilizerComponentImage D).subtype)) : MovedMinimal D := by
  let σ := (movedStabilizerAction D).comp (movedStabilizerComponent D).subtype
  let f := ((actionHom (movedStabilizerAction D)).comp
    (movedStabilizerComponent D).subtype).rangeRestrict
  let : IsIrreducible σ := (irreducible_comp_surjective_iff f
    (MonoidHom.rangeRestrict_surjective _) _).mpr hi
  intro J hJW hLJ
  let W := ⁅D.fullModule,L⁆
  let P : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (J.subgroupOf W).toAddSubgroup
    apply_mem_toSubmodule l w hw := by
      exact (mem_normalizer_iff.mp (hLJ l.property) w.toMul.val).mp hw }
  rcases eq_bot_or_eq_top P with hbot | htop
  · right
    intro w hw
    have hp : Additive.ofMul (⟨w,hJW hw⟩ : W) ∈ P.toSubmodule := hw
    rw [hbot] at hp
    have hz : w = 1 := congrArg (fun v : Additive W => (v.toMul : G))
      (show Additive.ofMul (⟨w,hJW hw⟩ : W) = 0 from hp)
    exact hz ▸ (centralizer (L : Set G)).one_mem
  · left
    apply le_antisymm hJW
    intro w hw
    have hp : Additive.ofMul (⟨w,hw⟩ : W) ∈ P.toSubmodule := by rw [htop]; trivial
    exact hp

/-- Suzuki moved minimality follows as soon as one original starred actor
moves the component; no constituent or quotient-faithfulness premise is used. -/
theorem movedMinimal_of_suzuki_moving_starred_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hmove : ¬ A ≤ centralizer (movedStabilizerComponentImage D :
      Set (actionImage (movedStabilizerAction D)))) : MovedMinimal D := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  let ρ := movedStabilizerAction D
  let S := movedStabilizerComponentImage D
  let eS := (originalMovedComponentEquiv D c.nonnormal).trans e
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv (originalMovedComponentEquiv D c.nonnormal).symm
  have hS := (original_component_quotient_sqtk D).knownSimple_of_equiv
    (originalMovedComponentEquiv D c.nonnormal).symm
  exact movedMinimal_of_image_component_irreducible D
    (suzuki_irreducible_of_moving_starred_actor (imageRepresentation ρ)
      (imageRepresentation_injective ρ) (imageRepresentation_isIrreducible ρ
        (movedStabilizerAction_irreducible D c ht htn hsep)) S hS m hm eS A hA hmove)

/-- The actual original Hall exponent in the moving-starred Suzuki branch. -/
theorem hall_exponent_of_suzuki_moving_starred_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hmove : ¬ A ≤ centralizer (movedStabilizerComponentImage D :
      Set (actionImage (movedStabilizerAction D)))) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1 :=
  hall_exponent_of_suzuki_and_moved_minimal D c hnot m hm e
    (movedMinimal_of_suzuki_moving_starred_actor D c m hm e A hA hmove)

/-- A starred actor centralizing the original component must move an actual
component orbit in the same centralizer. The soluble three-core alternative
is excluded by its fixed-space plane. -/
theorem original_centralizing_starred_component_support
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hAc : A ≤ centralizer (movedStabilizerComponentImage D :
      Set (actionImage (movedStabilizerAction D)))) :
    ∃ J : Subgroup (actionImage (movedStabilizerAction D)),
      IsComponent _ J ∧ J ≤ (originalMovedQuotientAction D c.nonnormal).ker ∧
      componentOrbit J A ≤ (originalMovedQuotientAction D c.nonnormal).ker ∧
      componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A := by
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let S := movedStabilizerComponentImage D
  let C := centralizer (S : Set (actionImage ρ))
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let eS := originalMovedComponentEquiv D c.nonnormal
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS.symm
  have hi := imageRepresentation_isIrreducible ρ
    (movedStabilizerAction_irreducible D c ht htn hsep)
  have hSn : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S hSn
  have hfixed := fixedSpace_eq_bot_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S hSn
  have hAn : A ⊓ C ≠ ⊥ := by
    rw [inf_eq_left.mpr hAc]
    exact hA.1.2.1.1
  obtain ⟨X,hXC,hAX,hXn,hXA,hcase⟩ :=
    ChosenSource325.exists_starred_moved_subgroup_in_component_centralizer σ
      (imageRepresentation_injective ρ) S
      (movedStabilizerImage_twoCore_eq_bot D c ht htn hsep) hfull hA hAn
  have hXA' : ⁅X,A⁆ = X := by
    have hAC : A ⊓ C = A := inf_eq_left.mpr hAc
    change ⁅X,A ⊓ C⁆ = X at hXA
    rwa [hAC] at hXA
  rcases hcase with ⟨hXP,_⟩ | ⟨J,hJ,hJC,hXJ⟩
  · have hP : (pCore 3 C).map C.subtype ≤ pCore 3 (actionImage ρ) :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map C.subtype⟩
    exact (ChosenSource325.starred_not_centralizing_of_moved_three_core σ
      (imageRepresentation_injective ρ) S hfull hfixed hA X hXC
      (hXP.trans hP) hAX hXn hXA' hAc).elim
  · have hker := originalMovedQuotientAction_kernel D c.nonnormal
    exact ⟨J,hJ,hJC.trans hker.symm.le,hXJ ▸ hXC.trans hker.symm.le,
      hXJ ▸ hXn,hXJ ▸ hXA'⟩

/-- Every component orbit supporting a centralizing starred actor has
order divisible by three. Both normalized and exchanged Suzuki support
are excluded on the unchanged moved module. -/
theorem original_centralizing_starred_support_three_dvd
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hJ : IsComponent _ J)
    (hJC : J ≤ (originalMovedQuotientAction D c.nonnormal).ker)
    (hmove : ⁅componentOrbit J A,A⁆ = componentOrbit J A) : 3 ∣ Nat.card J := by
  by_contra hthree
  have h3 := Nat.prime_three.coprime_iff_not_dvd.mpr hthree
  obtain ⟨r,hr,⟨eJ⟩⟩ := movedStabilizerImage_component_suzuki D c ht htn hsep J hJ h3
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let S := movedStabilizerComponentImage D
  let := hJ.2
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv (originalMovedComponentEquiv D c.nonnormal).symm
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : Nontrivial S := (originalMovedComponentEquiv D c.nonnormal).symm.injective.nontrivial
  have hi := imageRepresentation_isIrreducible ρ
    (movedStabilizerAction_irreducible D c ht htn hsep)
  have hnot : ¬ A ≤ normalizer (J : Set (actionImage ρ)) := by
    intro hn
    have ho : componentOrbit J A = J :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn) (le_componentOrbit J A)
    have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible σ
      (imageRepresentation_injective ρ) hi S ((Subgroup.nontrivial_iff_ne_bot S).mp inferInstance)
    have hJn : J ≠ ⊥ := by
      let : Fact (0 < r) := ⟨hr⟩
      let : Nontrivial J := eJ.symm.injective.nontrivial
      exact (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
    apply ChosenSource325.no_normalized_suzuki_support σ (imageRepresentation_injective ρ)
      S J A A hfix (hJC.trans (originalMovedQuotientAction_kernel D c.nonnormal).le)
      (movedStabilizerImage_component_sqtk D J hJ) hJn hn hA le_rfl _ hr eJ
    simpa only [ho] using hmove
  have hlay := movedStabilizerImage_semisimple_sqtk D
    (componentLayer (actionImage ρ)) componentLayer_idempotent
  have hindex : (normalizer (J : Set (actionImage ρ))).index = 2 :=
    (hJ.normal_or_index_two_of_layer_odd_rank_le_two hlay.stronglyQuasithin).resolve_left
      (fun hj => hnot (by
        let := hj
        exact le_top.trans (show normalizer (J : Set (actionImage ρ)) = ⊤ from normalizer_eq_top J).ge))
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
  let N := normalizer (J : Set (actionImage ρ))
  let : N.Normal := normal_of_index_eq_two hindex
  have hdiv : N.relIndex A ∣ 2 := by
    simpa only [show N.index = 2 from hindex] using N.relIndex_dvd_index_of_normal A
  have hirel : N.relIndex A = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hdiv).resolve_left
      (fun he => hnot (Subgroup.relIndex_eq_one.mp he))
  have horbit : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two J A N hirel inf_le_right ha han
  exact ChosenSource325.not_starred_exchanged_suzuki_support σ (imageRepresentation_injective ρ)
    (movedStabilizerImage_twoCore_eq_bot D c ht htn hsep) J A hJ hindex a ha han horbit hA r hr eJ


/-- The literal Suzuki Hall branch is complete unless every starred actor
centralizes the original component. In that residual case a chosen actor
moves a genuine three-divisible component orbit in the exact quotient kernel.
Neither the constituent nor moved minimality is an input. -/
theorem hall_exponent_or_suzuki_centralizing_component_support
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (m : ℕ) (hm : 0 < m)
    (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    (∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1) ∨
    ((∀ A : Subgroup (actionImage (movedStabilizerAction D)),
        A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) →
        A ≤ (originalMovedQuotientAction D c.nonnormal).ker) ∧
      ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
        A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
        IsComponent _ J ∧ 3 ∣ Nat.card J ∧
        J ≤ (originalMovedQuotientAction D c.nonnormal).ker ∧
        componentOrbit J A ≤ (originalMovedQuotientAction D c.nonnormal).ker ∧
        componentOrbit J A ≠ ⊥ ∧ ⁅componentOrbit J A,A⁆ = componentOrbit J A) := by
  by_cases hall : ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2^n+1
  · exact Or.inl hall
  right
  have hcentral (A : Subgroup (actionImage (movedStabilizerAction D)))
      (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
      A ≤ centralizer (movedStabilizerComponentImage D :
        Set (actionImage (movedStabilizerAction D))) := by
    by_contra hmove
    exact hall (hall_exponent_of_suzuki_moving_starred_actor D c hnot m hm e A hA hmove)
  refine ⟨fun A hA => (hcentral A hA).trans
    (originalMovedQuotientAction_kernel D c.nonnormal).symm.le,?_⟩
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hsep := original_seed_separated_of_suzuki D c m hm e ht htn
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr
    (movedStabilizerAction_cubic_bound D c ht htn hsep)
  obtain ⟨J,hJ,hJK,hXK,hXn,hXA⟩ :=
    original_centralizing_starred_component_support D c ht htn hsep A hA (hcentral A hA)
  exact ⟨A,J,hA,hJ,original_centralizing_starred_support_three_dvd D c ht htn hsep
    A J hA hJ hJK hXA,hJK,hXK,hXn,hXA⟩
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
