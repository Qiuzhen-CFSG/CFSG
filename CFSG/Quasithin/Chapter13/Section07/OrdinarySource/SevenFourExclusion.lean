module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SevenFourModule
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedNormalizerRank
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.NormalizerTheta
public import CFSG.Quasithin.Chapter13.Section05.AmbientSource.ParabolicCentralizer
public import Theory.Representation.BinaryAlternatingSevenControl.PlaneStabilizer
public import Theory.Representation.BinaryConjugationSection

/-!
# Excluding the contained four-dimensional A₇ component

The marked irreducible section identifies the full U_H/V₁ module with the
specified four-space, since its central covering kernel is zero. The original
seed has dimension two. Its model stabilizer has three-rank two, and the
literal component quotient map transfers this rank to N_K(V₃).
Original 13.7.5(4) then forces the covered local quotient, whose central
three-group contradicts the ordinary A₆ quotient.

All original source hypotheses and the specified K/O₂(K) action marking
are retained. The argument uses the arbitrary four-dimensional action;
no identification with the six-dimensional alternating natural module occurs.

Source: Aschbacher–Smith, 13.7.5(4), 13.7.6(4), printed pp.938–939,
in the ordinary branch of 13.7.18, printed p.945.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

/-- The actual seed normalizer has three-rank two in the contained A₇ four-space case. -/
theorem seven_four_seed_normalizer_rank
    (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) E)
    (hfaith : Function.Injective τ) (hirr : IsIrreducible τ)
    (hd : Module.finrank (ZMod 2) E = 4)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) :
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 2 := by
  let : FiniteDimensional (ZMod 2) E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨eV,he⟩ := seven_four_full_module_of_one_le d hH hF9 hKH hK hL₁K ρ hρ τ hirr hd eK hs
  rw [seed_normalizer_rank_of_model (d.line_le_plane.trans d.plane_le_seed)
    hKH ρ hρ τ eK eV he]
  apply BinaryAlternatingSevenControl.plane_stabilizer_rank τ hfaith hd
  exact (eV.finrank_map_eq _).trans
    (sectionImage_seed_finrank (d.line_le_plane.trans d.plane_le_seed) d.line_card d.seed_card)

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions

namespace CFSG.Quasithin.Chapter13.Section07.OrdinarySource
open Section08.SourceCompletion Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Original 13.7.6(4) for a component containing L₁ in the ordinary A₆ setup. -/
theorem alternating_seven_four_false
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
    {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) E)
    (hfaith : Function.Injective τ) (hirr : IsIrreducible τ)
    (hd : Module.finrank (ZMod 2) E = 4)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH τ eK) : False := by
  have hr := ModelExclusions.seven_four_seed_normalizer_rank
    d hH h hKH hK hL₁K ρ hρ τ hfaith hirr hd eK hs
  obtain ⟨e⟩ := (ModelExclusions.covered_and_theta_of_one_le_rank_two
    d h1221 hH h
    (Section05.AmbientSource.source_parabolic_centralizer d eL h1221 hm)
    hKH hK hL₁K hr).1
  have hc := Nat.card_congr (centerCongr (e.symm.trans eL)).toEquiv
  rw [Representation.Hexacode.even_center_card,
    alternatingGroup.center_eq_bot (by simp),card_bot] at hc
  omega

end CFSG.Quasithin.Chapter13.Section07.OrdinarySource
