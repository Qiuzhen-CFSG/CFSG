module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.ChiefGeneration.Representation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FourLocalFactors.ChiefGeneration.LiteralAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.NaturalSection

/-!
# L₁ difference generation in the natural four-dimensional case

We retain the universal earlier chief-factor calculation of 13.7.6(3a) as
an explicit theorem input at the fixed genuine standing configuration. Its
natural-section premise is constructed using `natural_section_model`, with
the actual relative component quotient equivalence. Two noncentral chief
factors then exhaust the four dimensions and generate the entire module.

The printed statement of 13.7.6(3a) counts factors on U_H. The proof on
printed p.939 explicitly calculates two noncentral factors on Ũ_H. The
separate input below records this latter calculation, without identifying
the two carriers or assuming an unproved transfer through V₁. It extends
the existing `Earlier1376` interface without changing that shared module.
No use is made of the transvection-dependent theorem 13.8.5.

The final theorem supports the `ConjugationSection` carrier used by source
assembly: relative normality, the elementary quotient, its actual action,
and the transport of difference generation are all constructed. The later
commutator lift and local-plane assembly remain in their existing modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.6(3a),
printed pp.938–939 (PDF pp.955–956), especially its proof's explicit Ũ_H
calculation; 13.8.6(4), printed p.948 (PDF p.965).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration
open CriticalGeometry.Reorientation TransvectionRecognition TransvectionRecognition.Component
open TransvectionParabolic.Marking.NaturalSection
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G : Type*} [Group G]

/-- The universal degree-six chief-factor calculation in the proof of
13.7.6(3a), at one fixed standing setup. Its conclusion concerns the literal
U_H/V₁ with the actual L₁ action. The global source hypotheses belong to the
theorem supplying this input, just as for `Earlier1376`. -/
def Earlier1376ChiefFactors [Finite G] (L₁ T G₁ M V₃ V₁ : Subgroup G) : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Source.Hz L₁ T G₁ M),
    V₁ ≤ Source.UH H V₃ →
    ∀ [_hn : (V₁.subgroupOf (Source.UH H V₃)).Normal]
      [_ha : IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
      (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (K : Subgroup G) (hKH : K ≤ H), (K.subgroupOf H).IsCComponent →
      ∀ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6),
      HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK →
        TwoNoncentralChiefFactors (ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp
          (inclusion (le_sup_left.trans hH.1.2))))

/-- An extension of the existing earlier-theorem interface, retaining its
clauses and the additional quotient calculation from the source proof.
This is an input specification, not a proof of the earlier theorem. -/
structure Earlier1376WithChiefFactors [Finite G]
    (L L₁ T G₁ M V₂ V₃ V₁ : Subgroup G) : Prop where
  earlier : Earlier1376 L L₁ T G₁ M V₂ V₃ V₁
  chiefFactors : Earlier1376ChiefFactors L₁ T G₁ M V₃ V₁

/-- Apply the earlier calculation only after constructing its natural-section
premise, then use the complete chief-series dimension argument. -/
theorem literal_coinvariants_eq_top [Finite G]
    (L₁ T G₁ M H K V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (earlier : Earlier1376ChiefFactors L₁ T G₁ M V₃ V₁)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      E (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (E v)) :
    Coinvariants.ker (ρ.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion (le_sup_left.trans hH.1.2)))) = ⊤ := by
  have hc := earlier H hH hV₁ ρ hρ K hKH hK
    ((Components.componentStarEquiv H K hKH hK).trans eK)
    (natural_section_model K hKH hK ρ hρ eK E he)
  have hd : Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 4 := by
    rw [E.finrank_eq, finrank_natural_even (Fin 6) (by decide)]
    rfl
  exact ker_eq_top_of_two_noncentral _ hd hc

/-- The required L₁ difference generation for the actual H* conjugation
section, in the arbitrary carrier used by `SourceAssembly`. The only earlier
input added here is the precise universal chief-factor clause above. -/
theorem coinvariants_eq_top_of_earlier [Finite G]
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    (L₁ T G₁ M H K V₃ V₁ : Subgroup G)
    (earlier : Earlier1376ChiefFactors L₁ T G₁ M V₃ V₁)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (η : Representation (ZMod 2) (Source.Hstar H) U)
    (s : ConjugationSection H (Source.UH H V₃) V₁ η)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : U ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      E (η k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (E v)) :
    Coinvariants.ker (η.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (inclusion (le_sup_left.trans hH.1.2)))) = ⊤ := by
  let := section_normal s
  let := section_elementary s
  have hmodel : ∀ (k : Source.starImage H K) v,
      ((sectionLinearEquiv s).trans E) (literalAction s k v) =
        alternatingNaturalRepresentation (Fin 6) (eK k) (((sectionLinearEquiv s).trans E) v) := by
    intro k v
    change E (sectionLinearEquiv s (literalAction s k v)) = _
    rw [literalAction_equivariant, he]
    rfl
  have hg := literal_coinvariants_eq_top L₁ T G₁ M H K V₃ V₁ earlier hH s.line_le hKH hK
    (literalAction s) (literalAction_isConjugation s) eK ((sectionLinearEquiv s).trans E) hmodel
  apply ker_eq_top_of_equivariant _ _ (sectionLinearEquiv s) _ hg
  intro g v
  exact literalAction_equivariant s _ v
end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors.ChiefGeneration

end
