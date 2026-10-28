module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.TransvectionSource

/-!
# The first critical case in the middle-node branch

The original 13.8.5 recognition theorem supplies the actual whole-module
models at the literal quotient action. Their actor orders exclude S₈.
Consequently the middle-node marking cannot occur in case (1) of 13.8.8;
only its strict critical-pair case remains for the orthogonal argument.

Source: Aschbacher–Smith, 13.8.25, printed pp.959–960/PDF pp.976–977.
The preceding 13.7.6 and G.6.4 inputs retain their existing source contracts.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
open TransvectionRecognition TransvectionRecognition.Component.ModelExtension
open TransvectionRecognition.Component.RecognitionStep
open FourStructure.ChiefFactors
open Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
  (localEarlier : Solvable.EarlierLocalInputs (G := G))
  (hG64 : G64SourceTheorem.{u} KnownSimple.IsKnownSimple)
  (hH : H ∈ Source.Hz (sourceOne L T V₁) T G₁ M)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
  (hρ : IsSourceAction H V₃ V₁ ρ)

include d earlier localEarlier hG64 hH hρ

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- The literal source action of an S₈ overgroup has no transvections. -/
theorem no_transvection_of_symmetric_eight
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8)) (a : Source.Hstar H) :
    fixedCodim ρ (zpowers a) ≠ 1 := by
  intro ha
  have hc : Nat.card (Source.Hstar H) = 40320 := by
    rw [Nat.card_congr eH.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hm := TransvectionSource.transvection_models d earlier localEarlier hG64 hH ρ hρ a ha
  unfold Seven.LocalGeometry.TransvectionModels at hm
  rcases hm with hs | hl | ⟨_, e, _, _⟩
  · obtain ⟨e⟩ := hs
    rw [Nat.card_congr e.toEquiv] at hc
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
  · obtain ⟨e⟩ := hl
    have he : Nat.card (PSL 4) = 20160 := by
      rw [Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [Nat.card_congr e.toEquiv, he] at hc
    norm_num at hc
  · rw [Nat.card_congr e.toEquiv] at hc
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc

omit [(V₁.subgroupOf (Source.UH H V₃)).Normal] in
/-- Application to the S₈ marking constructed by the original parabolic
argument, preserving its component quotient and its literal source action. -/
theorem middle_node_no_transvection
    {K : Subgroup G} (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hm : Parabolics.MiddleNodeMarking H K (sourceOne L T V₁) T hKH hK e)
    (a : Source.Hstar H) : fixedCodim ρ (zpowers a) ≠ 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, eH, _⟩ := hm
  exact no_transvection_of_symmetric_eight d earlier localEarlier hG64 hH ρ hρ eH a

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OriginalSource
