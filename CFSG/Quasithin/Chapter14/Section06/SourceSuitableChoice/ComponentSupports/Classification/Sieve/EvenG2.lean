module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.Symplectic
public import Theory.SpecificGroups.G2Even.BorelThreeRank
public import Theory.AtlasPort.LinearGroups.G2.Perfectness

/-!
# Even-degree G₂ exclusion and the remaining terminal catalogue

The marked component Borel lies in the literal image of M intersect K,
whose three-rank is at most one. For G₂ in even binary degree, the two
split-torus parameters give rank at least two in that Borel. This excludes
the even-degree G₂ branch without assuming component normality.

Together with the symplectic and odd-degree exclusions, the final consumers
leave only even-degree rank-one models, binary or even-degree PSL₃, A₆,
and odd-degree nonbinary G₂ in the normal component catalogue. All markings
refer to the original K/O₂(K), and the terminal specialization keeps H=Mc.
The remaining rows and natural-support assembly stay with
qt-e-suitable-component-supports; original 14.6.18 stays with
qt-e-14625-source. This is a further sieve, not the completed 14.6.20 list.

Source: Aschbacher--Smith 14.6.20, printed p.1037. The octonion torus and
Sylow normalizer calculations use the attributed ATLAS model; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08.Components.Models
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

omit hab in
/-- Every marked component Sylow normalizer has three-rank at most one. -/
theorem source_component_borel_threeRank_le_one
    {D : Type*} [Group D] [Finite D]
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* D)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K) :
    primeRank 3 (normalizer (((P : Subgroup K).map
      (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))) : Set D)) ≤ 1 := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have hp := source_component_sylow_normalizer_le_image T M hsolv H hH.1 K hKH hK eK P hP
  exact (primeRank_mono 3 hp).trans
    (source_component_overlap_image_threeRank_le_one hG T hempty hM hunique hmany hcard e
      H hH K hKH q (hk.symm ▸ pCore_isPGroup))

omit hab in
/-- The actual even-degree G₂ torus contradicts the component Borel rank. -/
theorem source_component_not_even_g2
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 2 ≤ f) (he : Even f) :
    ¬ IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ f) := by
  rintro ⟨F,_,_,hF,⟨eF⟩⟩
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) (by omega)
  let : Group.IsPerfect (Atlas.G2.Model F) := Atlas.G2.isPerfect hlarge
  let ec : commutator (Atlas.G2.Model F) ≃* Atlas.G2.Model F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  let eK := eF.trans ec
  obtain ⟨P,hP⟩ := source_component_sylow T H K hH.1.2 hKH hK
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Pq := P.mapSurjective (f := q) (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  have hu := source_component_borel_threeRank_le_one hG T hempty hM hunique hmany hcard e hsolv
    H hH K hKH hK eK P hP
  have hl := Atlas.G2.two_le_sylow_normalizer_threeRank_of_even_degree hF he Pq
  change primeRank 3 (normalizer (Pq : Set (Atlas.G2.Model F))) ≤ 1 at hu
  omega

/-- The binary and even-degree exclusions leave only odd exponents at least three. -/
theorem source_component_g2_odd_degree
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    {f : ℕ} (hf : 1 ≤ f) (hm : IsG2DerivedAt (K ⧸ pCore 2 K) (2 ^ f)) :
    3 ≤ f ∧ Odd f := by
  have hne : f ≠ 1 := by
    rintro rfl
    exact source_component_not_binary_g2_model hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK (by simpa only [pow_one] using hm)
  have ho : Odd f := (Nat.even_or_odd f).resolve_left fun he =>
    source_component_not_even_g2 hG T hempty hM hunique hmany hcard e hsolv
      H hH K hKH hK (by omega) he hm
  exact ⟨by obtain ⟨k,hk⟩ := ho; omega,ho⟩

/-- The actual normal catalogue after both symplectic parities and the
nonbinary even-degree G₂ branch have been discharged. -/
@[expose] def NormalRemainingQuotientModels (D : Type*) [Group D] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSL D 2 (2 ^ f)) ∨
  (∃ f : ℕ, 2 ≤ f ∧ Even f ∧ ClassicalGroup.IsPSU D 3 (2 ^ f)) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (f = 1 ∨ Even f) ∧ ClassicalGroup.IsPSL D 3 (2 ^ f)) ∨
  Nonempty (D ≃* alternatingGroup (Fin 6)) ∨
  (∃ f : ℕ, 3 ≤ f ∧ Odd f ∧ IsG2DerivedAt D (2 ^ f))

/-- Apply the new exclusions to the instantiated source catalogue. -/
theorem source_normal_component_remaining_models
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : NormalRemainingQuotientModels (K ⧸ pCore 2 K) := by
  have hm := source_normal_component_even_lie_models hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK hn
  rcases hm with h2 | hu | h3 | ⟨f,hf,_,hs⟩ | ⟨f,hf,hg⟩
  · exact Or.inl h2
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      (source_component_sp_four_alternating_six hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hf hs))))
  · obtain ⟨hf3,ho⟩ := source_component_g2_odd_degree hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK (by omega) hg
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨f,hf3,ho,hg⟩)))

/-- The refined normal catalogue on the original terminal H=Mc. -/
theorem terminal_normal_component_remaining_models
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : (K.subgroupOf Mc).Normal) : NormalRemainingQuotientModels (K ⧸ pCore 2 K) :=
  source_normal_component_remaining_models hG T hempty hM hunique hmany hcard e hab hsolv Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK hn

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
