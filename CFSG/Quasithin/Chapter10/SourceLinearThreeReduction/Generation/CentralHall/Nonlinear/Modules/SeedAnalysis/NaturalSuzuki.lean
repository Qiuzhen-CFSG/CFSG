module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalKernelCubic
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.GeneralizedFitting.LayerRankOrbit

/-!
# The exchanged Suzuki pair in the natural kernel

The actual full-normalizer image has an SQTK cover. Theorem A therefore
controls its semisimple subgroups, and A.3.6 identifies every three-free
component as a concrete Suzuki group. For the component already extracted
from the original starred actor, normalization contradicts the Suzuki
endpoint: the commuting perfect natural component forces a strict ratio
drop on an invariant Suzuki constituent, whose ratio is at least two.

The ambient odd-rank bound on the semisimple layer then forces the same
actor to exchange exactly two Suzuki components. The final application
retains the literal marked quotient kernel, its proper nontrivial
intersection with the actor, the commutator identity, and the actual
Suzuki isomorphism. This removes the normalized-component branch of
D.3.9(2); excluding the exchanged pair and discharging source separation
remain with qt-d-10-nona5-central-hall-orders.

The component classification and endpoint proofs reuse the completed
Chapter 11 and chosen-seed arguments with the original Chapter 10 action.
Source: Aschbacher--Smith A.3.6, D.3.8--9 and D.3.21,
printed pp.44--46,199--201 and204--207.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite

/-- The actual SQTK cover controls semisimple subgroups of the action image. -/
theorem movedStabilizerImage_semisimple_sqtk
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : ChapterA.Section02.IsSemisimple J) : IsSQTK KnownSimple.IsKnownSimple J := by
  let c := (movedStabilizerImage_sqtkQuotient D).some
  let q := c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel)
  have hq : Function.Surjective q := c.equiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hs : ChapterA.Section02.IsSectionOf J c.Cover :=
    (ChapterA.Section02.IsSectionOf.subgroup J).ambient_surjective q hq
  exact ⟨ChapterA.Section02.TheoremA.stronglyQuasithin_section
    ChapterA.Section02.theoremA_knownSimple c.sqtk.stronglyQuasithin c.sqtk.isKGroup hs hJ,
    hs.isKGroup c.sqtk.isKGroup⟩

/-- Every component inherits SQTK through its semisimple section. -/
theorem movedStabilizerImage_component_sqtk
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : IsComponent _ J) : IsSQTK KnownSimple.IsKnownSimple J := by
  let := hJ.2
  apply movedStabilizerImage_semisimple_sqtk D J
  apply top_unique
  exact le_sSup (show IsComponent J ⊤ from
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩)

/-- A three-free component of the actual normalizer image is a concrete Suzuki group. -/
theorem movedStabilizerImage_component_suzuki
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (h3 : Nat.Coprime 3 (Nat.card J)) :
    ∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) := by
  let := hJ.2
  have hJ2 : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hJ.1,movedStabilizerImage_twoCore_eq_bot D c ht htn hsep]
    exact J.subtype.ker_eq_bot_iff.mpr J.subtype_injective
  have htop : IsComponent J ⊤ :=
    ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv : (⊤ : Subgroup J) ≃* J).symm⟩
  have hclass := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    J (movedStabilizerImage_component_sqtk D J hJ) hJ2 ⊤ htop.isCComponent
  have h3top : Nat.Coprime 3 (Nat.card (⊤ : Subgroup J)) := by
    simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup J) ≃* J).toEquiv] using h3
  obtain ⟨r,hr,⟨e⟩⟩ :=
    Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.Catalogue.a36_suzuki_of_coprime
      hclass h3top
  exact ⟨r,by omega,⟨(topEquiv : (⊤ : Subgroup J) ≃* J).symm.trans e⟩⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The normalized-component branch in the actual kernel contradicts the
Suzuki lower bound and the strict starred-constituent ratio drop. -/
theorem natural_starred_kernel_component_not_normalized
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hJK : J ≤ (movedNaturalImageQuotientAction D e I E hE).ker)
    (hm : ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
      componentOrbit J A) (hne : componentOrbit J A ≠ ⊥) :
    ¬ A ≤ normalizer (J : Set (actionImage (movedStabilizerAction D))) := by
  intro hn
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedNaturalImageQuotientAction D e I E hE
  let S := movedStabilizerComponentImage D
  have horbit : componentOrbit J A = J :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn) (le_componentOrbit J A)
  have hJn : J ≠ ⊥ := horbit ▸ hne
  have h3 : Nat.Coprime 3 (Nat.card J) := by
    apply (naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE
      3 (by decide) ?_).of_dvd_right (card_dvd_of_le hJK)
    rw [Nat.card_congr e.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two _
  obtain ⟨r,hr,⟨eJ⟩⟩ := movedStabilizerImage_component_suzuki D c ht htn hsep J hJ h3
  obtain ⟨⟨eS⟩,hC⟩ := movedNaturalImage_component_and_centralizer D e I E hE
  let := hJ.2
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : Nontrivial S := eS.injective.nontrivial
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S ((Subgroup.nontrivial_iff_ne_bot S).mp inferInstance)
  apply ChosenSource325.no_normalized_suzuki_support σ (imageRepresentation_injective ρ)
    S J A (A ⊓ α.ker) hfix (hJK.trans hC.le)
    (movedStabilizerImage_component_sqtk D J hJ) hJn hn hA inf_le_left _ hr eJ
  simpa only [horbit] using hm

private theorem exchanged_component_pair
    {X : Type*} [Group X] [Finite X] (A J : Subgroup X)
    (hJ : IsComponent X J)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p (componentLayer X) ≤ 2)
    (hnot : ¬ A ≤ normalizer (J : Set X)) :
    (normalizer (J : Set X)).index = 2 ∧
      ∃ a : X, a ∈ A ∧ a ∉ normalizer (J : Set X) ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
  have hi : (normalizer (J : Set X)).index = 2 :=
    (hJ.normal_or_index_two_of_layer_odd_rank_le_two hrank).resolve_left
      (fun hj => hnot (by
        let := hj
        exact le_top.trans (show normalizer (J : Set X) = ⊤ from normalizer_eq_top J).ge))
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨hi,a,ha,han,?_⟩
  let N := normalizer (J : Set X)
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex A ∣ 2 := by
    simpa only [show N.index = 2 from hi] using N.relIndex_dvd_index_of_normal A
  have hirel : N.relIndex A = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun he => hnot (Subgroup.relIndex_eq_one.mp he))
  exact componentOrbit_eq_sup_of_index_two J A N hirel inf_le_right ha han

local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- The remaining original natural branch has a genuinely exchanged Suzuki
pair in the same proper nontrivial actor kernel. -/
theorem source_natural_starred_actor_suzuki_pair
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    Odd n ∧ ∃ A J : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      1 < rank A ∧
      ⊥ < A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker < A ∧
      IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      (∃ r : ℕ, 0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r)) ∧
      ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
        componentOrbit J A ∧ componentOrbit J A ≠ ⊥ ∧
      (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2 ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧
        a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))) ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨ho,A,hA,hr,hbot,hproper,J,hJ,hJK,h3,_h5,hm,hne⟩ :=
    source_natural_starred_actor_mixed_kernel D c ht htn hsep n hn e I hI E hE
  have hnot := natural_starred_kernel_component_not_normalized D c ht htn hsep e I E hE
    A J hA hJ hJK hm hne
  have hlay := movedStabilizerImage_semisimple_sqtk D
    (componentLayer (actionImage (movedStabilizerAction D))) componentLayer_idempotent
  obtain ⟨hi,a,ha,han,horbit⟩ := exchanged_component_pair A J hJ
    hlay.stronglyQuasithin hnot
  exact ⟨ho,A,J,hA,hr,hbot,hproper,hJ,hJK,
    movedStabilizerImage_component_suzuki D c ht htn hsep J hJ h3,hm,hne,hi,a,ha,han,horbit⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
