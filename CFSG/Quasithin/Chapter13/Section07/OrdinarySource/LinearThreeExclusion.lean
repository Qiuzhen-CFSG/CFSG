module
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeFamily
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleQuotient
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeMiddleResidue
public import CFSG.Quasithin.Chapter13.Section07.OrdinarySource.LinearThreeResidues
/-!
# Exclusion of the ordinary binary natural-three component

The actual vertices LT, K₀L₂T and H form a C₃ system. Their quotients are S₆,
S₃ × S₃ and PSL₃(2), their common chamber is the original Sylow subgroup T,
and the original generated subgroup has trivial two-core. The local two-core
has order greater than 32 by the chief-factor count, so C₃ recognition applies.
It forces the third vertex H to have trivial center, contradicting the original
nontrivial line V₁ centralized by H.

All middle-vertex quotient and rank-two residue hypotheses are discharged on
the literal source subgroups. The final wrapper preserves the raw special-linear
natural representation and the original component quotient map.

Source: Aschbacher–Smith, 13.7.6(1), printed p.940, used in 13.7.18, p.945.
-/

public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
open LinearThreeFamily LinearThreeC3Local Quasithin.I5
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

/-- The original ordinary source excludes the full binary natural-three action. -/
theorem linear_three_general_linear_false
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) : False := by
  obtain ⟨eJ⟩ := middle_quotient d hH h hU hV hm hKH hK hL₁K ρ hρ eK hs
  have hc := LinearThreeResidues.source_family_chamber (K := K) d hH h hU hV
  have hpoint := LinearThreeResidues.source_family_point_parabolics (K := K) d hH h hU hV
  have hline := LinearThreeMiddleResidue.source_middle_rankTwo
    d hH h hm hKH hK hL₁K ρ hρ eK hs eJ hc
  have hplane := LinearThreeResidues.source_family_plane_parabolics
    d hH h hU hV hKH hK hL₁K ρ hρ eK hs
  obtain ⟨eH,_,_,_⟩ := ModelExclusions.linear_three_full_action_of_one_le
    d hH h hKH hK hL₁K ρ hρ eK hs
  let c := BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)
  exact source_false_of_C3_system d h
    (source_system d h hU hV (middle_le_generated hKH) hc eJ (eH.trans c.symm)
      hpoint hline hplane) rfl

/-- The binary special-linear natural-three row is impossible in the ordinary source. -/
theorem linear_three_false
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (specialLinearNatural 3) eK) : False := by
  let c := BinaryLinear.OuterCyclic.slEquivLinear 3
  have hs' : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) (eK.trans c) := by
    obtain ⟨hst,e,he⟩ := hs
    exact ⟨hst,e,he⟩
  exact linear_three_general_linear_false d hH h hU hV hm hKH hK hL₁K ρ hρ (eK.trans c) hs'

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
