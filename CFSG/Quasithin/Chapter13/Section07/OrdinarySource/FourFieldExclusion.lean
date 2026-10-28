module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SylowFixedSpace
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.FixedCubic
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.Representation.BinaryConjugationSection

/-!
# The contained four-field natural components are impossible

The original point residual and full component Sylow generate a solvable
subgroup, hence preserve the model's Sylow fixed line. Transitivity on the
original seed puts its image in that line. Cubic actors fixing the line
fix its lifts through the actual central cover and normalize the original
seed. Its solvable theta subgroup cannot cover the nonsolvable cubic
closure in the point local subgroup's SL₂(4) quotient.

These exclusions retain the original ordinary A₆ setup, F.9.1 hypotheses,
raw conjugation section and literal K/O₂(K) marking. The centralizer input
is discharged by the original13.5.4(4) source theorem.
Source: Aschbacher–Smith13.7.6(5),13.7.18, printed pp.939,945.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition
open Section08.TransvectionRecognition.Component
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- The marked natural SL₃(4) component is excluded in the original contained branch. -/
theorem linear_three_four_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (_hUH : IsMulCommutative (Section08.Source.UH H V₃))
    (_hfull : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (_c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearNatural F 3) eK) : False := by
  have hfour : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  exact ModelExclusions.source_model_sylow_fixer_false d h1221 hH h
    (Section05.AmbientSource.source_parabolic_centralizer d eL h1221 hm)
    hKH hK hL₁K ρ hρ (linearNatural F 3) eK hs
    (Matrix.PSL3.LinearThree.four_solvable_sylow_overgroup_normalizes hfour)
    (Matrix.PSL3.LinearThree.four_sylow_fixed_cubic_not_solvable hfour)

/-- The marked natural Sp₄(4) component is excluded in the original contained branch. -/
theorem symplectic_four_four_false
    [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (_hUH : IsMulCommutative (Section08.Source.UH H V₃))
    (_hfull : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (_c : BinaryConjugationSection H (Section08.Source.UH H V₃) V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))))
    (F : BinaryField) (hF : F.degree = 2)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (binarySymplectic F) eK) : False := by
  have hfour : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  exact ModelExclusions.source_model_sylow_fixer_false d h1221 hH h
    (Section05.AmbientSource.source_parabolic_centralizer d eL h1221 hm)
    hKH hK hL₁K ρ hρ (binarySymplectic F) eK hs
    (Theory.SpecificGroups.SymplecticFour.solvable_sylow_overgroup_normalizes (by omega))
    (Theory.SpecificGroups.SymplecticFour.four_sylow_fixed_cubic_not_solvable hfour)

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
