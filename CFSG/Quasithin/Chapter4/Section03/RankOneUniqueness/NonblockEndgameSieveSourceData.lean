module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceOddRows

/-!
# The corrected secondary record on the literal sieve action

Every image uses the original normalQuotientAction on the full component
quotient. Projection and core movement reuse the subgroup-level source lemmas.
Prime extraction requires nontrivial torus image explicitly: the unsupported
whole-radical torus movement is neither assumed nor reconstructed.
These interfaces connect the corrected record to the source model inspection.
Source: Aschbacher--Smith, original 4.3.12--16, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}
namespace SecondarySourceData

/-- All source images share the same literal quotient action. -/
def image (s : SecondarySourceData c n) (B : Subgroup G) :
    Subgroup (MulAut (s.component ⧸ pCore 2 s.component)) :=
  (B.subgroupOf (rootNormalizer c)).map s.action

abbrev torusImage (s : SecondarySourceData c n) := image s s.torus
abbrev secondaryImage (s : SecondarySourceData c n) := image s (secondary c)
abbrev radicalImage (s : SecondarySourceData c n) := image s (R₂ c)
abbrev coreImage (s : SecondarySourceData c n) := image s (Q c)
abbrev secondaryCoreImage (s : SecondarySourceData c n) := image s ((secondary c).pCoreIn 2)

def componentImage (s : SecondarySourceData c n) :
    Subgroup (MulAut (s.component ⧸ pCore 2 s.component)) := s.component.map s.action

def ambientImage (s : SecondarySourceData c n) :=
  componentImage s ⊔ radicalImage s ⊔ torusImage s

/-- The proposed generation input concerns the whole radical on this action. -/
def ActionGeneration (s : SecondarySourceData c n) : Prop :=
  coreImage s ⊔ ⁅radicalImage s, secondaryImage s⁆ = radicalImage s

/-- This is an explicit sufficient premise, not a field of the source record. -/
def CoreImageCentral (s : SecondarySourceData c n) : Prop :=
  secondaryCoreImage s ≤ centralizer (secondaryImage s : Set _)

/-- The literal source inclusion before passage to any quotient. -/
abbrev secondaryToComponent (s : SecondarySourceData c n) :=
  SourceImages.secondaryToComponent c s.component s.secondary_le

omit [Finite G] in
/-- The inclusion preserves the actual embedded secondary subgroup. -/
theorem secondaryToComponent_injective (s : SecondarySourceData c n) :
    Function.Injective (secondaryToComponent s) :=
  SourceImages.secondaryToComponent_injective c s.component s.secondary_le

/-- The literal projection to the full quotient, including its center. -/
abbrev secondaryProjection (s : SecondarySourceData c n) :=
  SourceImages.secondaryProjection c s.component s.secondary_le

/-- Its rank-one quotient is the original one. -/
theorem secondaryProjection_model (s : SecondarySourceData c n) :
    ClassicalGroup.IsPSL ((secondaryProjection s).range ⧸
      pCore 2 (secondaryProjection s).range) 2 (2^n) :=
  SourceImages.secondaryProjection_model c s.component s.secondary_le s.secondary_model

/-- The source secondary projection remains perfect. -/
theorem secondaryProjection_perfect (s : SecondarySourceData c n) :
    Group.IsPerfect (secondaryProjection s).range :=
  SourceImages.secondaryProjection_perfect c s.component s.secondary_le

omit [Finite G] in
/-- The component image is exactly inner conjugation on its full quotient. -/
theorem componentImage_eq_inner (s : SecondarySourceData c n) :
    componentImage s = MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) := by
  let := s.normal
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨QuotientGroup.mk' (pCore 2 s.component) ⟨x,hx⟩,
      (normalQuotientAction_inner s.component (pCore 2 s.component) ⟨x,hx⟩).symm⟩
  · rintro ⟨q,rfl⟩
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 s.component) q
    exact ⟨x,x.property,normalQuotientAction_inner s.component (pCore 2 s.component) x⟩

/-- Only the core movement is asserted for the corrected source record. -/
theorem coreImage_moved (s : SecondarySourceData c n) :
    ⁅coreImage s,torusImage s⁆ = coreImage s := s.core_action_moved

/-- Ambient whole-radical generation passes through the literal source action. -/
theorem actionGeneration_of_generation (s : SecondarySourceData c n)
    (hg : Q c ⊔ ⁅R₂ c,secondary c⁆ = R₂ c) : ActionGeneration s :=
  s.action_generation_of_generation hg

omit [Finite G] in
/-- Cyclicity descends through the literal action. -/
theorem torusImage_cyclic (s : SecondarySourceData c n) : IsCyclic (torusImage s) := by
  let := s.torus_cyclic
  let := isCyclic_of_surjective (subgroupOfEquivOfLe s.torus_le).symm
    (subgroupOfEquivOfLe s.torus_le).symm.surjective
  exact isCyclic_of_surjective (s.action.subgroupMap _) (s.action.subgroupMap_surjective _)

/-- Prime extraction explicitly retains the missing nontrivial-image premise. -/
theorem torus_prime_action_of_nontrivial_image (s : SecondarySourceData c n)
    (hn : 0 < n) (hne : torusImage s ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧
      ∃ y : rootNormalizer c, (y : G) ∈ s.torus ∧ orderOf (s.action y) = p := by
  let := s.normal
  exact SourceImages.torus_prime_action_of_nontrivial_image c s.component hn
    s.torus s.torus_le s.torus_card hne

/-- Centrality plus generation supplies nontrivial torus action legitimately. -/
theorem torusImage_ne_bot_of_central_core_and_generation (s : SecondarySourceData c n)
    (hc : CoreImageCentral s) (hg : ActionGeneration s) : torusImage s ≠ ⊥ := by
  let := s.normal
  intro ht
  exact s.radical_action (SourceImages.radical_eq_bot_of_torus_eq_bot c s.component s.torus
    (s.secondary_le.trans (map_subtype_le _)) s.radical_le s.torus_le
    s.radical_normalizer hc s.core_moved hg ht)

end SecondarySourceData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
