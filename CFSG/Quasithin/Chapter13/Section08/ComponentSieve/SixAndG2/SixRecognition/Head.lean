module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked.ChiefFactors

/-!
# Recovering the literal component section from a central head kernel

Let W be an invariant subspace of U_H/V₁, centralized by K, whose quotient
has the marked natural action. Generation U_H=[U_H,K] makes the literal
commutator image all of U_H/V₁. The natural module has no K-fixed vectors,
so W is exactly the fixed space, not merely a central subspace. The first
isomorphism theorem then constructs the required component-section model.
The intrinsic quotient marking is obtained from K* using the canonical
K/O₂(K) equivalence. The final theorem applies the existing full source
alternative, including the L₁ chief-factor conclusion.

The head and centrality hypotheses must be supplied by the strict-case
multiple-factor exclusion and the appendix classification, or by 13.8.5
in the equality case. This module does not assert those inputs.

Source: Aschbacher–Smith 13.8.26, last paragraph, printed p.962.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension NaturalSix

variable {G : Type*} [Group G] [Finite G] {H K V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

omit [Finite G] in
/-- An epimorphism with central kernel identifies the *literal* component
section. The fixed-kernel equality is proved using the actual A₆ action. -/
theorem section_of_natural_quotient
    (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eK : (K ⧸ pCore 2 K) ≃* Alternating)
    (p : Additive (Source.Utilde H V₃ V₁) →ₗ[ZMod 2] Natural)
    (hp : Function.Surjective p)
    (he : ∀ (k : K) v,
      p (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        alternatingAction (eK (QuotientGroup.mk' (pCore 2 K) k)) (p v))
    (hk : p.ker ≤ fixedSpace ρ (Source.starImage H K)) :
    HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK := by
  let S := commutatorImage H V₃ V₁ K
  let F := fixedInCommutator H V₃ V₁ ρ K
  let j : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] S :=
    (LinearEquiv.ofTop S (commutatorImage_eq_top hgen)).symm
  let q : S →ₗ[ZMod 2] Natural := p.comp S.subtype
  have hq : Function.Surjective q := by
    intro v
    obtain ⟨u, rfl⟩ := hp v
    exact ⟨j u, by change p (j u).val = p u; rw [LinearEquiv.coe_ofTop_symm_apply]⟩
  have hker : q.ker = F := by
    apply le_antisymm
    · intro u hu
      exact hk hu
    · intro u hu
      change p u = 0
      apply Marked.residual_fixed_eq_zero
      intro a ha
      let a' : Alternating := ⟨a, Marked.residual_le_alternating ha⟩
      obtain ⟨k, hka⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (eK.symm a')
      have hka' : eK (QuotientGroup.mk' (pCore 2 K) k) = a' := by rw [hka]; simp
      have hfix := hu (⟨QuotientGroup.mk' (pCore 2 H) (inclusion hKH k),
        ⟨inclusion hKH k, k.property, rfl⟩⟩ : Source.starImage H K)
      change ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u = u at hfix
      have hh := he k u
      rw [hfix, hka'] at hh
      exact hh.symm
  let e : ComponentSection H V₃ V₁ ρ K ≃ₗ[ZMod 2] Natural :=
    (Submodule.quotEquivOfEq F q.ker hker.symm).trans (q.quotKerEquivOfSurjective hq)
  refine ⟨commutatorImage_invariant K hKH ρ hρ, e, ?_⟩
  intro k u
  change p (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u) =
    alternatingAction (eK (QuotientGroup.mk' (pCore 2 K) k)) (p u)
  exact he k u

/-- Centrality of the head kernel suffices; no recognition of the whole
source module or of the component section is assumed. -/
theorem section_of_central_head
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eC : Source.starImage H K ≃* Alternating)
    (W : Subrepresentation ρ) (hW : W.toSubmodule ≤ fixedSpace ρ (Source.starImage H K))
    (E : (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule) ≃ₗ[ZMod 2] Natural)
    (hE : ∀ (a : Source.starImage H K) v,
      E (W.quotientRepresentation a v) = alternatingAction (eC a) (E v)) :
    let eK := (Components.componentStarEquiv H K hKH hK).trans eC
    HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK := by
  let p := E.toLinearMap.comp W.toSubmodule.mkQ
  apply section_of_natural_quotient hKH ρ hρ hgen _ p
    (E.surjective.comp W.toSubmodule.mkQ_surjective)
  · intro k v
    have h := hE (Components.componentStarEquiv H K hKH hK
      (QuotientGroup.mk' (pCore 2 K) k)) (W.toSubmodule.mkQ v)
    rw [Subrepresentation.quotientRepresentation_mk, Components.componentStarEquiv_mk] at h
    exact h
  · intro v hv
    apply hW
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact E.injective (hv.trans (map_zero E).symm)

/-- The actual source consumer retains the intrinsic K quotient and obtains
both full modules, both possible actors and the L₁ marking from the head. -/
theorem source_alternative_of_central_head
    (T : Sylow 2 G) {L V V₂ M G₁ : Subgroup G}
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : EarlierInputs T L V V₁ V₂ V₃ M G₁)
    (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (eC : Source.starImage H K ≃* Alternating)
    (W : Subrepresentation ρ) (hW : W.toSubmodule ≤ fixedSpace ρ (Source.starImage H K))
    (E : (Additive (Source.Utilde H V₃ V₁) ⧸ W.toSubmodule) ≃ₗ[ZMod 2] Natural)
    (hE : ∀ (a : Source.starImage H K) v,
      E (W.quotientRepresentation a v) = alternatingAction (eC a) (E v)) :
    let eK := (Components.componentStarEquiv H K hKH hK).trans eC
    let := d.uh_elementary hH
    HasSectionModel H V₃ V₁ ρ K hKH alternatingAction eK ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Alternating) ∧
      SourceSix.MarkedFullAction hKH eK ρ ∧
      CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
        (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ (sourceOne L T V₁)
          (le_sup_left.trans hH.1.2) ρ) := by
  let := d.uh_elementary hH
  have hs := section_of_central_head hKH hK ρ hρ hgen eC W hW E hE
  exact ⟨hs, SourceSix.source_alternative_of_section T d earlier hH hKH hK ρ hρ _ hs⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SixRecognition
end
