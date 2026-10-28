module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoCore
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoG2Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2Irreducibility
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2Source
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity

/-!
# Whole-core contracts and conditional assembly of small C.1.32

There are three central-core quotient rows. The binary row already gives
C.1.32(5). In each other row, the reconstruction input must describe the
entire U=[O₂(L),L], including elementary abelianness and centrality in O₂(L).
The A₆ input retains both the natural action and the exceptional triple-cover
alternative. The G₂ input identifies the actual central quotient of U with
the canonical natural action; its irreducibility is proved by the model API.

The group clauses of shortness and relative blockhood follow from the MS-pair.
This yields the unchanged five-way `RankTwoAlternatives` and constructs the
existing earlier-classification record when C.1.34 is also supplied. The two
reconstruction implications are explicit independent inputs, not proved
classification theorems. `OriginalSource/RankTwoReconstruction` applies this
assembly to the actual source marking and the original 15.3.25 consumer.

Source: Aschbacher--Smith C.1.7, C.1.30--34, printed pp.123,135--137;
Meierfrankenfeld--Stellmacher (1993), Main Theorem (2),(6),(10).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The whole-core output still needed in the Sp₄(2)′ central-quotient row.
The second model retains the triple-cover center, core order and faithfulness. -/
structure AlternatingSixReconstruction (L : Type*) [Group L] : Prop where
  elementary : IsElementaryAbelian 2 (blockU L)
  central : blockU L ≤ centralizer (pCore 2 L : Set L)
  irreducible : BlockModuleIrreducible L
  model : IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) ∨
    (Nat.card (center (L ⧸ pCore 2 L)) = 3 ∧
      Nat.card (blockU L) = 2 ^ 6 ∧ centralizer (blockU L : Set L) = pCore 2 L)

/-- The whole-core output still needed in the G₂(2)′ row, with its actual
conjugation action on the trace-zero octonions modulo scalars. -/
structure G2Reconstruction (L : Type*) [Group L] : Prop where
  elementary : IsElementaryAbelian 2 (blockU L)
  central : blockU L ≤ centralizer (pCore 2 L : Set L)
  model : Nonempty (BlockModuleModel L g2TwoNaturalAction)

/-- Reconstruct C.1.32(2) or (4), including relative blockhood, from the
full A₆-row module output. No reconstruction implication is asserted here. -/
theorem SmallMSPair.rankTwo_of_alternatingSix_reconstruction (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))
    (r : AlternatingSixReconstruction L) : RankTwoAlternatives L R := by
  let eA := e.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hq := h.core_quasisimple_of_centralCore eA
  have hs := h.short_of_core r.elementary r.central hq r.irreducible
  rcases r.model with hm | ⟨hz, hu, hf⟩
  · exact Or.inr (Or.inl ⟨h.block_of_short hs, by
      exact ⟨by decide, hs, hm⟩⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.block_of_short hs,
      hs, hq, hz, ⟨(centralPreimageQuotientEquiv (pCore 2 L)).symm.trans eA⟩, hu, hf⟩)))

/-- Convert the canonical whole-core natural action to the literal G₂
block predicate consumed by C.1.32(1). -/
theorem SmallMSPair.rankTwo_of_g2_reconstruction (h : SmallMSPair κ L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2)))
    (r : G2Reconstruction L) : RankTwoAlternatives L R := by
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.isSimple_commutator_binary
  obtain ⟨m⟩ := r.model
  have hs := h.short_of_core r.elementary r.central
    (h.core_quasisimple_of_centralCore e) m.g2_irreducible
  exact Or.inl ⟨h.block_of_short hs,
    G2Source.to_source (ChapterC.IsG2TwoBlock.of_model hs ⟨m⟩)⟩

/-- The independent A₆-row reconstruction theorem to be supplied. -/
def AlternatingSixReconstructionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J), SmallMSPair κ L R →
    ((L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) → AlternatingSixReconstruction L

/-- The independent G₂-row reconstruction theorem to be supplied. -/
def G2ReconstructionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J), SmallMSPair κ L R →
    ((L ⧸ centralPreimage (pCore 2 L)) ≃*
      commutator (Atlas.G2.Model (ZMod 2))) → G2Reconstruction L

/-- Assemble all three input rows. The binary row is proved already;
the other two reconstruction implications remain explicit premises. -/
theorem SmallMSPair.rankTwo_of_reconstruction
    (ha : AlternatingSixReconstructionInput κ) (hg : G2ReconstructionInput κ)
    (h : SmallMSPair κ L R) : RankTwoAlternatives L R := by
  rcases h.rankTwo with hb | ha6 | hg2
  · obtain ⟨e⟩ := hb
    exact h.rankTwo_of_binary e
  · obtain ⟨e⟩ := ha6
    exact h.rankTwo_of_alternatingSix_reconstruction e (ha G L R h e)
  · obtain ⟨e⟩ := hg2
    exact h.rankTwo_of_g2_reconstruction e (hg G L R h e)

/-- Supply the existing source record from the two reconstruction inputs
and the separate C.1.34 theorem, preserving both public field types. -/
theorem earlierMSClassifications_of_reconstruction
    (ha : AlternatingSixReconstructionInput κ) (hg : G2ReconstructionInput κ)
    (linearThree : ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J),
      SmallMSPair κ L R → ∀ (n : ℕ), 1 ≤ n →
      ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ S : Subgroup J, Chapter1.IsSylowIn 2 S (L ⊔ R) → R ≤ S →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
          Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.MSModuleAlternatives
            L R S n F e) : EarlierMSClassifications κ :=
  ⟨fun _ _ _ _ _ h => h.rankTwo_of_reconstruction ha hg, linearThree⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
