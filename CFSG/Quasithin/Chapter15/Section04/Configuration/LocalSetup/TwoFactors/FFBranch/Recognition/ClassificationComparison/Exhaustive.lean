module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.QuasisimpleComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.OuterGroupComparison
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.ExhaustiveSource
/-!
# Exhaustive comparison on the actual mixed FF quotient

The product and hyperplane branches give an actual S₃ × S₃ equivalence.
The group-only outer A₆–C₃ branch is impossible. The quasisimple comparison
retains L₃(2), A₆, S₆, A₇, S₇, the triple-six cover and the two G₂(2) actors,
with the possible triple-symmetric-six ambient extension. All surviving
B.5.1 module clauses, including nonsplit and trivial extensions, stay on
the original offender action in `ComparedBranch`. Its ambient models have
compatible subgroup and action maps. No equality N = D is assumed.

The source-facing application proves O_{3'}(H) = O₂(H) from the classifier
on the actual offender group before transporting F.6.18 to H/O₂(H).
The complete F.6.11 implication is supplied by its elementary proof.
Only full universal F.6.18 and corrected B.5.1/adequate B.5.6 implications
remain authorized source inputs. Concrete module exclusions and the final
S₃ × S₃ identification remain with the recognition owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
15.4.18, p.1163; F.6.11/F.6.18, pp.306–310; B.5.1/B.5.6, pp.99–110.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
universe u v

/-- Actual quotient identification, or the checked small group and module
catalogue on the literal offender subgroup, with marked ambient extensions. -/
def ExhaustiveComparison {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) : Prop :=
  Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
    Nonempty (QuasisimpleComparison.ComparedBranch ρ)

/-- Exhaust every corrected full FF alternative and both orientations of all
retained Goldschmidt rows. The small list is a conclusion of the comparison. -/
theorem ProjectiveLine.ClassifiedAction.exhaustive_comparison
    {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
    (h : ProjectiveLine.ClassifiedAction K ρ G₁ G₂) : ExhaustiveComparison ρ := by
  cases h.ffAlternatives with
  | trivial ht =>
    let : Subsingleton (offenderSubgroup ρ) := ht
    let : Nontrivial (offenderSubgroup ρ) := FFAlternatives.nontrivial_of_ff _ h.ffWitness
    obtain ⟨g, hg⟩ := exists_ne (1 : offenderSubgroup ρ)
    exact (hg (Subsingleton.elim _ _)).elim
  | quasisimple hq c =>
    obtain ⟨b, _⟩ := h.compared_branch hq c
    exact Or.inr ⟨b⟩
  | symmetricThree c =>
    exact ((h.withLegacyAlternative (.symmetricThree c)).not_symmetricThree ⟨c.equiv⟩).elim
  | twoFactors c =>
    exact Or.inl (ProductComparison.product_comparison
      (h.withLegacyAlternative (.twoFactors c)) (Or.inl ⟨c⟩))
  | outerSixThree c =>
    exact (OuterGroupComparison.not_outerShape ρ h.twoCore h.goldschmidt
      h.ffHypothesis.generated h.quotient_twoGroup ⟨c.toGroupShape⟩).elim
  | hyperplane c =>
    exact Or.inl (ProductComparison.product_comparison
      (h.withLegacyAlternative (.hyperplane c)) (Or.inr (Or.inr ⟨c⟩)))

/-- A group-only view of the exhaustive result; the stronger result above
retains the original representation and all extension data for exclusions. -/
theorem ExhaustiveComparison.group_models
    {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} (h : ExhaustiveComparison ρ) :
    Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
      (QuasisimpleComparison.SmallActorModel (offenderSubgroup ρ) ∧
        QuasisimpleComparison.SmallAmbientModel D) := by
  rcases h with he | hb
  · exact Or.inl he
  · obtain ⟨b⟩ := hb
    exact Or.inr ⟨b.smallActor, b.ambient.smallAmbientModel⟩

variable {H : Type u} [Group H] [Finite H]

private theorem transport_quotient_lists (G₁ G₂ A B : Subgroup H)
    [A.Normal] [B.Normal] (h : A = B)
    (ht : ChapterF.IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' A))
      (G₂.map (QuotientGroup.mk' A)))
    (hf : GoldschmidtAlternatives.Remaining (G₁.map (QuotientGroup.mk' A))
      (G₂.map (QuotientGroup.mk' A))) :
    ChapterF.IsGoldschmidtTriple (G₁.map (QuotientGroup.mk' B))
      (G₂.map (QuotientGroup.mk' B)) ∧
    GoldschmidtAlternatives.Remaining (G₁.map (QuotientGroup.mk' B))
      (G₂.map (QuotientGroup.mk' B)) := by
  subst B
  exact ⟨ht, hf⟩

/-- Construct the full corrected actual-action record from the weaker adequate
classifier. The group-only outer case is excluded by the ambient comparison,
so no disputed splitting statement is required to construct this record. -/
theorem ProjectiveLine.classifiedAction_of_adequate_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) :
    pPrimeCore 3 H = pCore 2 H ∧ F611Preserved G₁ G₂ ∧
      ProjectiveLine.ClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection) := by
  obtain ⟨S, hS⟩ := (f611Conclusion_of_goldschmidt triple).core_sylow
  obtain ⟨hb, hw⟩ := offenderFFHypothesis_and_witness P Z hC hH Y₁ hF h₁ hZY
  have ha := sourceB.general _ _ _ hb
  have hq := quotient_offenderGroup_isTwoGroup P Z hC Y₁ Y₂ hgen h₁ h₂ hJ
  have hk := threePrimeCore_eq_twoCore_of_offender_core P Z hC S hS hq
    (ha.threePrimeCore_eq_bot _ hb hw)
  obtain ⟨hp, hf⟩ := ProjectiveLine.apply_F618_of_goldschmidt source618 hH G₁ G₂ triple different
  obtain ⟨ht, hf'⟩ := transport_quotient_lists G₁ G₂ _ _ hk hp.triple hf
  have hfull : FFAlternatives.ProjectiveLine.SourceAlternative (offenderAction P Z hC) := by
    cases ha with
    | trivial h => exact .trivial h
    | quasisimple hq c => exact .quasisimple hq c
    | symmetricThree c => exact .symmetricThree c
    | twoFactors c => exact .twoFactors c
    | outerSixThree c =>
      exact (OuterGroupComparison.not_outerShape (quotientAction P Z hC)
        coreQuotient_twoCore hf' hb.generated hq ⟨c⟩).elim
    | hyperplane c => exact .hyperplane c
  refine ⟨hk, hp, quotientAction_injective P Z hC, coreQuotient_twoCore,
    threePrimeCore_eq_twoCore_iff.mp hk, ht, hf', hb, hw, hfull, hq, ?_⟩
  exact ⟨P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H)),
    quotientAction_sylow_fixedSpace_kernel P Z hC⟩

/-- The exhaustive mixed-quotient comparison from raw intrinsic data. The
canonical quotient is H/O₂(H), the actor is its actual offender subgroup, and
F.6.11 is proved. Only the universal source classifiers remain inputs. -/
theorem exhaustive_comparison_of_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) :
    pPrimeCore 3 H = pCore 2 H ∧ F611Preserved G₁ G₂ ∧
      ProjectiveLine.ClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection) ∧
      ExhaustiveComparison (quotientAction P Z hC) := by
  obtain ⟨hk, hp, h⟩ := ProjectiveLine.classifiedAction_of_adequate_goldschmidt
    source618 sourceB hH G₁ G₂ triple different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ
  exact ⟨hk, hp, h, h.exhaustive_comparison⟩

/-- The stronger full corrected source interface also gives the exhaustive
comparison, retaining exactly the same actual quotient and module conclusion. -/
theorem ProjectiveLine.exhaustive_comparison_of_goldschmidt {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} K)
    (hH : IsSQTK K H) (G₁ G₂ : Subgroup H)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    (P : Sylow 2 H) (Z Y₁ Y₂ : Subgroup H)
    [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    (hF : Theory.GroupTheory.generalizedFitting H = pCore 2 H)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup H) = ⊤)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup H)).map coreProjection ≤
      offenderGroup P Z hC) :
    pPrimeCore 3 H = pCore 2 H ∧ F611Preserved G₁ G₂ ∧
      ProjectiveLine.ClassifiedAction K (quotientAction P Z hC)
        (G₁.map coreProjection) (G₂.map coreProjection) ∧
      ExhaustiveComparison (quotientAction P Z hC) :=
  CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.exhaustive_comparison_of_goldschmidt
    source618 sourceB.toAdequate hH G₁ G₂ triple
    different P Z Y₁ Y₂ hC hF hgen h₁ h₂ hZY hJ

/-- Apply the exhaustive comparison to the original ambient factors inside I.
Baumann containment transports both raw commutator identities. Y₂ needs no
membership in a T-invariant family. All quotient maps still belong to I. -/
theorem mixed_exhaustive_comparison
    {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
    (source618 : F618Universal K)
    (sourceB : FFAlternatives.ProjectiveLine.AdequateCompleteClassificationInput.{u,u} K)
    (T : Sylow 2 G) (I Y₁ Y₂ Z : Subgroup G) (P : Sylow 2 I)
    (G₁ G₂ : Subgroup I) (hI : IsSQTK K I)
    (triple : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (different : (pCore 2 G₁).map G₁.subtype ≠ (pCore 2 G₂).map G₂.subtype)
    [IsElementaryAbelian 2 (moduleClosure (Z.subgroupOf I))]
    (hC : centralizer (Z.subgroupOf I : Set I) = (P : Subgroup I))
    (hB : ChapterB.baumann (T : Subgroup G) ≤ (P : Subgroup I).map I.subtype)
    (hZI : Z ≤ I) (h₁I : Y₁ ≤ I) (h₂I : Y₂ ≤ I)
    (hF : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hgen : Y₁ ⊔ Y₂ ⊔ (P : Subgroup I).map I.subtype = I)
    (h₁ : Y₁ = ⁅Y₁, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (h₂ : Y₂ = ⁅Y₂, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hZY : ⁅Z, Y₁⁆ ≠ ⊥)
    (hJ : (Stellmacher.elementaryAbelianMaxJ (P : Subgroup I)).map coreProjection ≤
      offenderGroup P (Z.subgroupOf I) hC) :
    pPrimeCore 3 I = pCore 2 I ∧ F611Preserved G₁ G₂ ∧
      ProjectiveLine.ClassifiedAction K (quotientAction P (Z.subgroupOf I) hC)
        (G₁.map coreProjection) (G₂.map coreProjection) ∧
      ExhaustiveComparison (quotientAction P (Z.subgroupOf I) hC) := by
  have hJT := thompson_sylow_image_of_baumann I T P hB
  have hgen' : Y₁.subgroupOf I ⊔ Y₂.subgroupOf I ⊔ (P : Subgroup I) = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_sup, map_subgroupOf_eq_of_le h₁I,
      map_subgroupOf_eq_of_le h₂I, ← MonoidHom.range_eq_map, I.range_subtype]
    exact hgen
  exact exhaustive_comparison_of_goldschmidt source618 sourceB hI G₁ G₂ triple different
    P (Z.subgroupOf I) (Y₁.subgroupOf I) (Y₂.subgroupOf I) hC hF hgen'
    (factor_commutator_subgroupOf I Y₁ _ _ h₁I hJT h₁)
    (factor_commutator_subgroupOf I Y₂ _ _ h₂I hJT h₂)
    (seed_factor_commutator_ne_bot_subgroupOf I Z Y₁ hZI h₁I hZY) hJ

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
