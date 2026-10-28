module

public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.Original
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Solvable.NoTransvections

/-!
# The actual transvection normal closure in source 13.8.5

The point, natural-module and covered-factorization facts are supplied by
their proved source constructions. The original maximal-local hypothesis
gives the covered normalizer bound. The seed centralizer bound gives the
flag normalizer bound, while the original seed-core movement and F.9 give
the exact seed commutator. B.1.8 therefore excludes a solvable normal closure
of a transvection in the same H/O₂(H) action on U_H/V₁.

All inputs concern this original setup. No universal local-input family,
normal-closure solvability, selected factor or module model is assumed.
Source: Aschbacher--Smith, 13.8.5, printed pp.947--948.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
open TransvectionRecognition TransvectionRecognition.Solvable
open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- The literal normal closure of a transvection is nonsolvable, with every
local-source input constructed from the original standing geometry. -/
theorem original_normalClosure_not_solvable
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hmax : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥) :
    let := d.uh_elementary hH
    let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
    ∀ (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ → ∀ t : Source.Hstar H, IsTransvection ρ t →
      ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H))) := by
  let := d.uh_elementary hH
  let := (V₁.subgroupOf (Source.UH H V₃)).normal_of_isMulCommutative
  dsimp only
  intro ρ hρ t ht hsolv
  have hkernel : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (OddReduction.source_kernel hF9).symm.le
  have hrank := TwoFactors.source_threeRank_le_two d hH
  obtain ⟨b, hcount, hJ⟩ := source_normalClosure_factors
    (fun B _ _ _ σ => solvable_ff_factors B (Additive (Source.Utilde H V₃ V₁)) σ)
    ρ hρ hkernel hrank t ht hsolv
  have hc : b.count = 1 := by
    by_contra hne
    have htwo : b.count = 2 := by omega
    exact TwoFactors.source_two_factors_impossible T d earlier_marked_models hH
      ρ hρ t ht b hJ htwo
  have hmodels := local_flag_alternatives d
  have hfactor := fun W₁ W₃ (a : LocalAction.NaturalSetup L (T : Subgroup G) V W₁ W₃) =>
    CoverFactorization.source_factorization a
  have hdisp : V₁ = ⁅V₃, Source.QH H⁆ :=
    (Section07.source_commutator_conclusions (localNaturalSetup d) hF9 hH.2.1 hcomm).2.1.symm
  have hflag : normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤
      M ⊓ normalizer (V : Set G) := by
    simpa only [(localNaturalSetup d).first_normalizer] using
      Section05.PointAction.normalizer_intersection_source (localNaturalSetup d) hcentral
  rcases OneFactor.source_one_factor_alternatives T G₁ M hH hmodels hfactor
      hrank d.line_card d.seed_card ρ hρ t ht b hJ hc with
    hcentralizing | ⟨hres, hcover⟩ | ⟨_, hmoved⟩
  · have hgen := seed_generation_of_core_displacement d hH hmodels hfactor hdisp
    exact centralizing_one_factor_impossible ρ hρ (sourceOne L T V₁)
      (le_sup_left.trans hH.1.2) hgen hkernel t ht b hJ hc hcentralizing
  · exact hH.2.2 (le_M_of_preimageResidual_eq H M (zero L) _ hres
      (covered_normalizer_source d hmax hcover))
  · exact hH.2.2 (le_M_of_movedSpace_eq ρ hρ
      (d.line_le_plane.trans d.plane_le_seed) M (d.first_normalizer ▸ hH.2.1)
      (hflag.trans inf_le_left) _ hmoved)

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SolvableSource
