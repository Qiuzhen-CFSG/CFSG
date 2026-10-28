module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerRank
public import Theory.Representation.SL5ExteriorSquare.PointStabilizerRank
public import Theory.Quasithin.TwoKernelSubgroupRank

/-!
# The binary linear point ranks in the original component section

A model of the literal section [Ũ_H,K]/C_[Ũ_H,K](K) sends its point stabilizer
to the corresponding model stabilizer. Pull it back through the prescribed
map K → K/O₂(K) and the given actor equivalence. The kernel is exactly O₂(K),
so its three-rank is unchanged. The membership formula below retains every
original quotient map and every representative of the commutator image.

The natural modules in dimension at least five and both ten-dimensional
SL₅(2) exterior models supply rank two unconditionally. Classification also
supplies the bound for any ten-dimensional irreducible SL₅(2) module.
The earlier-source construction of the marked nonzero point and passage
from its section stabilizer to C_K(V₂) are separate from these model facts.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.7.6(1–2), printed pp.938–939, using the rank bound of 13.5.4(3).
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
open BinaryNaturalDual.VectorStabilizers
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointRanks
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08
variable {G : Type*} [Group G] [Finite G]
  (H V₃ V₁ K : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hKH : K ≤ H)

/-- The rank bound on the actual section-point stabilizer, identified on each
original K-representative. The invariance proof only makes the quotient class
a well-typed term; the membership formula determines the subgroup uniquely. -/
def SectionPointRankBound (u : commutatorImage H V₃ V₁ K) : Prop :=
  ∃ (hs : ∀ (k : K) (w : commutatorImage H V₃ V₁ K),
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) w ∈ commutatorImage H V₃ V₁ K)
    (P : Subgroup K), 2 ≤ primeRank 3 P ∧
      ∀ k : K, k ∈ P ↔
        (Submodule.Quotient.mk
          ⟨ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u, hs k u⟩ :
            ComponentSection H V₃ V₁ ρ K) = Submodule.Quotient.mk u

private theorem section_point_rank
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH σ eK)
    (hrank : ∀ v : E, v ≠ 0 → 2 ≤ primeRank 3 (representationStabilizer σ v))
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  let : Finite A := Finite.of_equiv (K ⧸ pCore 2 K) eK.toEquiv
  obtain ⟨hs, e, he⟩ := hmodel
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S := representationStabilizer σ (e (Submodule.Quotient.mk u))
  refine ⟨hs, S.comap q, ?_, ?_⟩
  · have hk : IsPGroup 2 q.ker := by
      have hker : q.ker = pCore 2 K := by
        dsimp only [q]
        rw [MonoidHom.ker_comp_of_injective _ _ eK.injective, QuotientGroup.ker_mk']
      rw [hker]
      exact pCore_isPGroup
    rw [primeRank_comap_eq_of_isTwoGroup_ker 3 (by decide) q
      (eK.surjective.comp (QuotientGroup.mk'_surjective _)) hk S]
    exact hrank _ (fun h => hu (e.injective (h.trans (map_zero e).symm)))
  · intro k
    change σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (e (Submodule.Quotient.mk u)) =
      e (Submodule.Quotient.mk u) ↔ _
    rw [← he k u, e.injective.eq_iff]

/-- The literal GLₙ(2) natural model used by the source recognition interface. -/
theorem natural_section_point_rank {n : ℕ} (hn : 5 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin n → ZMod 2))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation n) eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  apply section_point_rank H V₃ V₁ K ρ hKH (linearRepresentation n) eK hmodel _ u hu
  intro v hv
  exact BinaryLinear.PointStabilizerRank.two_le_linear_stabilizer (by simpa using hn) v hv

/-- The determinant-one natural model retains the same intrinsic K/O₂(K) map. -/
theorem specialLinear_section_point_rank {n : ℕ} (hn : 5 ≤ n)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural n) eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u := by
  apply section_point_rank H V₃ V₁ K ρ hKH (specialLinearNatural n) eK hmodel _ u hu
  exact fun v hv => BinaryLinear.PointStabilizerRank.two_le_natural_stabilizer hn v hv

/-- The square branch of the actual ten-dimensional source model. -/
theorem exterior_square_section_point_rank
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (SL5TenDimensional.exteriorAction 2) eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u :=
  section_point_rank H V₃ V₁ K ρ hKH _ eK hmodel
    SL5ExteriorSquare.PointStabilizerRank.two_le_square_stabilizer u hu

/-- The exterior cube is the source dual branch, with its literal action. -/
theorem exterior_cube_section_point_rank
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH (SL5TenDimensional.exteriorAction 3) eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u :=
  section_point_rank H V₃ V₁ K ρ hKH _ eK hmodel
    SL5ExteriorSquare.PointStabilizerRank.two_le_cube_stabilizer u hu

/-- I.1.6(7) discharges the model choice for any actual ten-dimensional irreducible. -/
theorem irreducible_ten_section_point_rank
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group E) [Representation.IsIrreducible σ]
    (hdim : Module.finrank (ZMod 2) E = 10)
    (eK : (K ⧸ pCore 2 K) ≃* SL5TenDimensional.Group)
    (hmodel : HasSectionModel H V₃ V₁ ρ K hKH σ eK)
    (u : commutatorImage H V₃ V₁ K)
    (hu : (Submodule.Quotient.mk u : ComponentSection H V₃ V₁ ρ K) ≠ 0) :
    SectionPointRankBound H V₃ V₁ K ρ hKH u :=
  section_point_rank H V₃ V₁ K ρ hKH σ eK hmodel
    (SL5ExteriorSquare.PointStabilizerRank.two_le_irreducible_ten_stabilizer σ hdim) u hu

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PointRanks
