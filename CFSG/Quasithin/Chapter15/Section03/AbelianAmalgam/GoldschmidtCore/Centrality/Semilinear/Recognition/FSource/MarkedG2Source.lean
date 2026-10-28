module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CyclicQuaternionModel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.WreathedRow
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource.CompleteReduction
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.G2
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.WreathedSylow
public import ABG.ChapterII.Section1.WreathedRegularModel

/-!
# F.6.18 row ten from the original marked derived G₂ amalgam

The actual G₂(2)′ common Sylow has the proved wreathed presentation. The
compatible source marking transports it and both concrete local cores to the
original groups. Their literal two-core quotients are supplied by the original
Goldschmidt hypothesis. The completed component catalogue and wreathed residual
argument then give all row-ten clauses, with no local-extension output premise.

Source: Aschbacher–Smith F.1.12(I)(8), F.6.5 and F.6.18(10), pp.263, 305, 310.
The genuine marked-amalgam enumeration remains with the F.1.12 source producer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
open ChapterF.GreenBook.ExceptionalModels
universe u
variable {κ : GroupClass.{u}} {G : Type u} [Group G] [Finite G]
    {G₁ G₂ : Subgroup G}

/-- The actual source marking supplies all three local inputs to row ten. -/
theorem derived_g2_marked_extensions
    (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : G2.IsDerivedAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Nonempty (S ≃* W32) ∧
      CyclicQuaternionExtension G₁ (Equiv.Perm (Fin 3)) ∧
      Extension G₂ C4Square (Equiv.Perm (Fin 3)) := by
  obtain ⟨_,_,hleft,hright⟩ := hM.local_structure
  have hW : Nonempty (G2.derivedB ≃* W32) :=
    Atlas.G2.BinaryParabolicPair.derivedSylow_isWreathedOfHeight.nonempty_mulEquiv_regularWreath
  refine ⟨⟨((MulEquiv.subgroupCongr hS.symm).trans hM.some.middle).trans hW.some⟩,
    ⟨pCore 2 G₁,inferInstance,⟨cyclicQuaternionProductOfModel hleft.some⟩,h.quotient_left⟩,
    ⟨pCore 2 G₂,inferInstance,hright,h.quotient_right⟩⟩

/-- The literal row-ten constructor from the original marked source branch. -/
theorem ten_of_marked_derived_g2
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hF : pResidual 2 G = generalizedFitting G)
    (hq : IsQuasisimple (pResidual 2 G))
    (hM : G2.IsDerivedAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    Alternative G₁ G₂ S := by
  let := q.coverGroup
  let := q.coverFinite
  obtain ⟨hS',hleft,hright⟩ := derived_g2_marked_extensions h S hS hM
  have hqF : IsQuasisimple (generalizedFitting G) := by
    let : IsQuasisimple (pResidual 2 G) := hq
    exact IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hF)
  have hK : IsComponent G (generalizedFitting G) :=
    ⟨(inferInstance : (generalizedFitting G).Normal).isSubnormal,hqF⟩
  exact ten_of_wreathed_source (hA _) (hC _) q.sqtk q.equiv.symm hK hF
    S hS' hleft hright

/-- No residual, component, field or local-recognition premise remains beyond
the genuine marked F.1.12 branch and the original A/C source hypotheses. -/
theorem source_of_marked_derived_g2
    (hA : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (H : Type u) [Group H] [Finite H], ChapterA.Section02.TheoremC κ H)
    (q : ThreePrimeSQTKQuotient κ G) (h : ChapterF.IsGoldschmidtTriple G₁ G₂)
    (S : Sylow 2 G) (hS : G₁ ⊓ G₂ = (S : Subgroup G))
    (hM : G2.IsDerivedAmalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    SourceAlternative G₁ G₂ S ∨ SourceAlternative G₂ G₁ S := by
  obtain ⟨T,hT,ha⟩ := source_alternative_or_large_quasisimple hA hC q h
  have he : T = S := Sylow.ext (hT.symm.trans hS)
  subst T
  rcases ha with ha | ⟨_,hF,hq⟩
  · exact ha
  · exact Or.inl (Or.inl (Or.inl (ten_of_marked_derived_g2 hA hC q h S hS hF hq hM)))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition.FSource
