module
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.IntersectionBalance.Models
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.Lifting
import Mathlib.Tactic

/-!
# Displacements on the literal source syntheme quotient

The same equivalence H* ≃ S₆ marks the source cosets, the natural/cover
action, and the radical. The actual noncentral permutation surjection and
source quadraticity exclude the coordinate four-groups. Conjugation in H
transfers the rank hypothesis from Uγ* to Uα*, so the finite radical theorem
gives order four and both corrected displacement equalities. The compatible
coordinates then transport them to the actual commutator image in UH/V₁.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34, printed p.968 (PDF p.985), using 13.8.4(5),(6).
The earlier model/parabolic identifications remain explicit local inputs.
-/

public section
open Subgroup Module Representation BinaryPermutation
open Representation.BinaryOffender Representation.SixLetterRadicalDisplacement
open Representation.SixLetterRadicalDisplacement.PermutationQuotients
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Apply the finite calculation to the literal marked cosets and the source quadratic subgroup.
The γ-to-α conjugator supplies the required lower bound on the actor order. -/
theorem source_radical_calculation (H M V V₃ Uα Uγ Vα R₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.VH H V)]
    (e : Source.Hstar H ≃* S)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ)
    (hq : IsQuadratic ρ (Source.starImage H Vα))
    (hUV : Source.starImage H Uα ≤ Source.starImage H Vα)
    (hVR : Source.starImage H Vα ≤ Source.starImage H R₁)
    (hR : (Source.starImage H R₁).map e.toMonoidHom = D)
    (hγH : Uγ ≤ H) (h : H)
    (hα : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα)
    (hr : 1 < rank (Source.starImage H Uγ)) :
    rank (Source.starImage H Uα) = 2 ∧
    naturalDisplacement ((Source.starImage H Uα).map e.toMonoidHom) = canonicalPlane ∧
    displacement ((Source.starImage H Uα).map e.toMonoidHom) = F ⊔ W := by
  classical
  let := Fintype.ofFinite (Source.Hstar H ⧸ Source.starImage H (H ⊓ M))
  obtain ⟨f, hf, he, hmove, _⟩ :=
    MarkedQuotient.symmetric_source H M V V₃ e hmark hflag hindex hnc hnorm ρ hρ
  let E := (Source.starImage H Uα).map e.toMonoidHom
  have hc : Nat.card E = Nat.card (Source.starImage H Uγ) := by
    dsimp only [E]
    rw [Subgroup.card_map_of_injective e.injective, ← hα,
      ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry.starImage_conjugate
        Uγ hγH h,
      Subgroup.card_map_of_injective (MulAut.conj _).injective]
  have hlarge : 2 < Nat.card E := by
    by_contra hn
    have hh := Nat.log_monotone (b := 2) (Nat.le_of_not_gt hn)
    rw [hc] at hh
    change rank (Source.starImage H Uγ) ≤ 1 at hh
    omega
  have hquad : IsQuadratic (ρ.comp e.symm.toMonoidHom) E := by
    intro x hx y hy v
    exact hq _ (hUV (Subgroup.mem_map_equiv.mp hx))
      _ (hUV (Subgroup.mem_map_equiv.mp hy)) v
  have hED : E ≤ D := by
    rw [← hR]
    exact map_mono (hUV.trans hVR)
  obtain ⟨hfour, hn, ha⟩ := radical_displacements_of_quadratic
    (ρ.comp e.symm.toMonoidHom) f hf
    (fun g v => by simpa using he (e.symm g) v)
    (by obtain ⟨g, v, hv⟩ := hmove; exact ⟨e g, v, by simpa using hv⟩)
    E hquad hED hlarge
  refine ⟨?_, hn, ha⟩
  rw [Subgroup.card_map_of_injective e.injective] at hfour
  change Nat.log 2 (Nat.card (Source.starImage H Uα)) = 2
  rw [hfour]
  decide

/-- The source fixed-space product, its rank-two quotient, and its actual commutator
image. Every displacement premise is discharged on the source syntheme quotient. -/
theorem source_model_calculation (H M V V₃ V₁ Uα Uγ Vα R₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (a : SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (e : Source.Hstar H ≃* S) (hm : CompatibleModel H V₃ V₁ a e)
    (hline : V₁ ≤ Source.UH H V₃)
    (hmark : (Source.starImage H (H ⊓ M)).map e.toMonoidHom = H2)
    (hflag : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnc : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hnorm : H ⊓ M ≤ normalizer (V : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Vsection H V V₃)))
    (hρ : SectionConjugation H V V₃ ρ)
    (hq : IsQuadratic ρ (Source.starImage H Vα))
    (hUV : Source.starImage H Uα ≤ Source.starImage H Vα)
    (hVR : Source.starImage H Vα ≤ Source.starImage H R₁)
    (hR : (Source.starImage H R₁).map e.toMonoidHom = D)
    (hγH : Uγ ≤ H) (h : H)
    (hα : Uγ.map (MulAut.conj (h : G)).toMonoidHom = Uα) :
    (∀ g, (∀ v ∈ quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃),
      tildeRepresentation H _ V₁ a g v = v) ↔ g ∈ Source.starImage H R₁) ∧
    finrank (ZMod 2) (Additive (Source.UH H V₃) ⧸
      inside (Source.UH H V₃) (Uone H _ V₁ a ⊔ V₃)) = 2 ∧
    (1 < rank (Source.starImage H Uγ) →
      rank (Source.starImage H Uα) = 2 ∧
      quotientSpace (Source.UH H V₃) V₁ (Uone H _ V₁ a ⊔ V₃) =
        quotientSpace (Source.UH H V₃) V₁ ⁅Source.UH H V₃, Uα⁆) := by
  obtain ⟨hfix, hdim⟩ := model_geometry H V₃ V₁ a e hm hline
  refine ⟨?_, hdim, ?_⟩
  · intro g
    rw [hfix, ← hR, Subgroup.mem_map_equiv, e.symm_apply_apply]
  · intro hr
    obtain ⟨hrank, hnat, haug⟩ := source_radical_calculation H M V V₃ Uα Uγ Vα R₁
      e hmark hflag hindex hnc hnorm ρ hρ hq hUV hVR hR hγH h hα hr
    have hαH : Uα ≤ H := by
      rw [← hα]
      rintro _ ⟨x, hx, rfl⟩
      exact H.mul_mem (H.mul_mem h.property (hγH hx)) (H.inv_mem h.property)
    exact ⟨hrank, model_displacement H V₃ V₁ Uα a e hm hαH hnat haug⟩

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.IntersectionBalance
