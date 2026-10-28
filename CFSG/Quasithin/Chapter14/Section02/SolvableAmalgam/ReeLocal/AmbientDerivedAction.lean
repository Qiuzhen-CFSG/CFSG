module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction.CoreCases
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction.Representation

/-!
# The ambient Ree and Tits derived actions and core normality

For an injectively embedded actual first parabolic, let P, E and F be the
images of its two-core, derived subgroup and derived centralizer. Starting
with O₂(Mc) ≤ P, the marked central involution in O₂(Mc), and the source
self-centralizer conditions before and after quotienting by that mark, the
literal preimage calculation gives O₂(Mc) = F or P.

Characteristicity in the surviving core gives normal E, and intrinsic
centralizer detection identifies C_Mc(E) with F. Conjugation on the published
binary coordinates therefore constructs a faithful Mc/F action fixing the
mark and restricting to the actual parabolic representation. Its translation
subgroup is the image of P; the existing point-stabilizer theorem makes P
normal, and maximality of the two-core gives O₂(Mc) = P.

The exports return the action with its equation for every ambient element
and every derived-coordinate vector. They assume neither an extended action
nor normality of P, E or F. These are conditional local theorems: the parent
retains their application under Hypothesis 14.2.1 and the later proof H = Mc.

Source: Aschbacher--Smith, Lemma 14.2.21 and chain (*), printed pp.988--989.
The corrected concrete parabolic calculations replace the incompatible
quotient-center assertion in the printed full-Ree argument.
-/

public section
open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
open ReeTwo.ParabolicConcrete ReeTwo.Centralizer
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction

/-- The full-Ree local conclusion from precisely the source core containments
and the two self-centralizer conditions. The faithful quotient action is constructed. -/
theorem ree_local {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    (hQ : pCore 2 M ≤ reeQ.map i) (hZQ : reeZ i ≤ pCore 2 M)
    (hZC : reeZ i ≤ center M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hs : QuotientCentralizerBound (pCore 2 M) (reeZ i)) :
    (reeE.map i).Normal ∧ centralizer (reeE.map i : Set M) = reeF.map i ∧
    (reeQ.map i).Normal ∧ pCore 2 M = reeQ.map i ∧
    ∃ (_ : (reeF.map i).Normal),
      ∃ ρ : M ⧸ reeF.map i →* stabilizer markedVector,
        Function.Injective ρ ∧
        (∀ g v, i (reeDerivedEmbedding (Multiplicative.ofAdd
            ((ρ (QuotientGroup.mk' _ g)).val v))) =
          g * i (reeDerivedEmbedding (Multiplicative.ofAdd v)) * g⁻¹) ∧
        (∀ h, ρ (QuotientGroup.mk' _ (i h)) = reeRepresentation h) := by
  obtain ⟨hEN, hC⟩ := ree_normal_centralizer i hi hc (ree_core_cases i hi hQ hZQ hc hs)
  let : (reeE.map i).Normal := hEN
  have hFN : (reeF.map i).Normal := by rw [← hC]; infer_instance
  let : (reeF.map i).Normal := hFN
  obtain ⟨ρ, hρ, heq, hres⟩ := ree_extended_action i hi hC (hZC (mem_zpowers _))
  have hPN := Parabolics.ree_core_normal_of_extended_action i ρ hρ hres
  have hP : reeQ.map i ≤ pCore 2 M := le_sSup ⟨hPN, pCore_isPGroup.map i⟩
  exact ⟨hEN, hC, hPN, le_antisymm hQ hP, hFN, ρ, hρ, heq, hres⟩

/-- The actual Tits local conclusion, using its literal core and derived-coordinate embedding. -/
theorem tits_local {M : Type*} [Group M] [Finite M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    (hQ : pCore 2 M ≤ titsQ.map i) (hZQ : titsZ i ≤ pCore 2 M)
    (hZC : titsZ i ≤ center M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hs : QuotientCentralizerBound (pCore 2 M) (titsZ i)) :
    (titsE.map i).Normal ∧ centralizer (titsE.map i : Set M) = titsF.map i ∧
    (titsQ.map i).Normal ∧ pCore 2 M = titsQ.map i ∧
    ∃ (_ : (titsF.map i).Normal),
      ∃ ρ : M ⧸ titsF.map i →* stabilizer markedVector,
        Function.Injective ρ ∧
        (∀ g v, i (titsDerivedEmbedding (Multiplicative.ofAdd
            ((ρ (QuotientGroup.mk' _ g)).val v))) =
          g * i (titsDerivedEmbedding (Multiplicative.ofAdd v)) * g⁻¹) ∧
        (∀ h, ρ (QuotientGroup.mk' _ (i h)) = titsRepresentation h) := by
  obtain ⟨hEN, hC⟩ := tits_normal_centralizer i hi hc (tits_core_cases i hi hQ hZQ hs)
  let : (titsE.map i).Normal := hEN
  have hFN : (titsF.map i).Normal := by rw [← hC]; infer_instance
  let : (titsF.map i).Normal := hFN
  obtain ⟨ρ, hρ, heq, hres⟩ := tits_extended_action i hi hC (hZC (mem_zpowers _))
  have hPN := Parabolics.tits_core_normal_of_extended_action i ρ hρ hres
  have hP : titsQ.map i ≤ pCore 2 M := le_sSup ⟨hPN, pCore_isPGroup.map i⟩
  exact ⟨hEN, hC, hPN, le_antisymm hQ hP, hFN, ρ, hρ, heq, hres⟩
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction
