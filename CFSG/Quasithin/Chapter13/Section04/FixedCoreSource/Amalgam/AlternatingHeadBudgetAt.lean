module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingHeadBudget
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingOrbitHeadsAt

/-!
# Guarded paired natural-head displacement

Embed both original orbit groups into the full omega span and add the
fixed-codimension contributions of their inequivalent natural quotients,
allowing the orbits to intersect. This bounds movement under every actual
component subgroup and exceeds the near-maximum budget when its image is
nontrivial elementary. AlternatingThompsonAt uses the full movement bound.
Source: Aschbacher--Smith 13.4.7(1iv), printed p.901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix
open Representation Representation.BinaryOffender
/-- Both original natural quotients contribute to movement on the whole
omega module, under the same actual component and parabolic marking. -/
theorem original_pair_alternating_paired_budget_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃* A6) :
    let C := K.map (A ⊔ B).subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion
          ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z (A ⊔ B)))))
      ∃ e : (C ⧸ pCore 2 C) ≃* A6,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        ((A.subgroupOf C).map f = a6DuadStabilizer ∧
          (B.subgroupOf C).map f = a6SynthemeStabilizer ∧
          ((T : Subgroup G).subgroupOf C).map f = a6Borel) ∧
        ∀ R : Subgroup C,
          (fixedCodim firstAlternating (R.map f) + fixedCodim secondAlternating (R.map f) ≤
            fixedCodim ρ R) ∧
          (IsElementaryTwo (R.map f) → rank (R.map f) + 1 < fixedCodim ρ R) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom (subgroupOfEquivOfLe hUX).symm.injective
  let := he
  let ρ := Representation.elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))))
  obtain ⟨e,hmarks,_,he₁,he₂,⟨p,hp⟩,⟨q,hq⟩,_⟩ :=
    original_pair_alternating_heads_at h₀ h structural D m hTA hTB eA eB hne hout
      hindexL hindexA hindexB hres h1332 K hK eK
  let := he₁
  let := he₂
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  let U₁ := conjugateSpanBy F₁ C
  let U₂ := conjugateSpanBy F₂ C
  let ρ₁ := Representation.elementaryRepresentation (p := 2)
    (U₁.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₁ C)))
  let ρ₂ := Representation.elementaryRepresentation (p := 2)
    (U₂.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F₂ C)))
  have h₁ : U₁ ≤ U := conjugateSpanBy_mono inf_le_left (map_subtype_le K)
  have h₂ : U₂ ≤ U := conjugateSpanBy_mono inf_le_left (map_subtype_le K)
  let i : ρ₁.IntertwiningMap ρ := {
    toLinearMap := (inclusion h₁).toAdditive.toZModLinearMap 2
    isIntertwining' c := by apply LinearMap.ext; intro x; rfl }
  let j : ρ₂.IntertwiningMap ρ := {
    toLinearMap := (inclusion h₂).toAdditive.toZModLinearMap 2
    isIntertwining' c := by apply LinearMap.ext; intro x; rfl }
  refine ⟨he,e,hmarks,?_⟩
  intro R
  refine ⟨paired_head_fixedCodim _ (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ρ ρ₁ ρ₂ i (inclusion_injective h₁) j (inclusion_injective h₂) p hp q hq R,?_⟩
  exact paired_heads_exceed_near_maximum_budget _
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
    ρ ρ₁ ρ₂ i (inclusion_injective h₁) j (inclusion_injective h₂) p hp q hq R

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
