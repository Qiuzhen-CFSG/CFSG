module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition.OppositeUpper.Source

/-!
# The strict-case consumer with both strong-offender callbacks discharged

Apply the direct upper permutation-quotient obstruction to W and U/W,
using their respective natural constituent markings. Both applications use
the same literal V_H/U_H and the same source γ-to-α conjugator. The
13.8.22–23 argument then excludes two faithful lower sections.

The preceding-source geometry and field hypotheses and the two natural
constituents remain explicit; their final assembly belongs to
`qt-d-138-six-section-recognition`. There is no remaining opposite-upper
callback or assumed four-dimensional upper quotient.

Source: Aschbacher–Smith 13.8.26, printed p.962/PDF p.979.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
open CriticalGeometry AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences

variable {G F : Type*} [Group G] [Finite G] [AddCommGroup F] [Module (ZMod 2) F]
  {L T H V V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The actual strict-case application. F.9.13 places Vγ; seed containment
then places Uγ, so no separate placement hypothesis for the offender is needed. -/
theorem source_no_two_faithful_sections_of_original_parabolic
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hf : Function.Injective ρ) (hVgH : c.Vgamma ≤ H)
    (hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom)
    (hline : Nat.card V₁ = 2)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (τ : Representation (ZMod 2) (Source.Hstar H) F)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ)
    (hquad : ⁅c.Ugamma V₃, ⁅c.Ugamma V₃, Source.VH H V⁆⁆ ≤ Source.UH H V₃)
    (hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hlarge : rank (Source.starImage H (c.Ugamma V₃)) = 1 →
      ∃ B : Subgroup (Source.Hstar H), Source.starImage H (c.Ugamma V₃) < B ∧
        ∀ b ∈ B, ∀ v ∈ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)),
          ρ b v - v ∈ s.image (c.Aone V₁))
    (W : Subrepresentation ρ)
    (mW : NaturalSection W.toRepresentation)
    (mQ : NaturalSection W.quotientRepresentation)
    (haW : alternatingGroup (Fin 6) ≤ mW.actor.range)
    (haQ : alternatingGroup (Fin 6) ≤ mQ.actor.range)
    (L₁ : Subgroup G) (hL : L₁ ≤ H) (hT : T ≤ H)
    (S : Sylow 2 (Source.Hstar H)) (hS : (S : Subgroup _) = Source.starImage H T)
    (hi : (Source.starImage H T).relIndex (Source.starImage H (L₁ ⊔ T)) = 3)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnorm : L₁ ⊔ T ≤ normalizer (V : Set G))
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (y : H) (hplace : c.Vgamma.map (MulAut.conj (y : G)).toMonoidHom ≤
      (L₁ ⊔ T).pCoreIn 2) : False := by
  let : Module.Finite (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) := Module.Finite.of_finite
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono hflag le_rfl)
  have hUgH := hUV.trans hVgH
  have hUp := (map_mono hUV).trans hplace
  exact source_no_two_faithful_sections c ρ s hf hUgH hreverse hline hcritical τ t
    hquad hA hbound hlarge W mW mQ
    (OppositeUpper.source_oppositeUpper_of_strong mW haW τ t L₁ (c.Ugamma V₃)
      hL hT hUgH S hS hi hflag hindex hnorm hnc hquad y hUp)
    (OppositeUpper.source_oppositeUpper_of_strong mQ haQ τ t L₁ (c.Ugamma V₃)
      hL hT hUgH S hS hi hflag hindex hnorm hnc hquad y hUp)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
end
