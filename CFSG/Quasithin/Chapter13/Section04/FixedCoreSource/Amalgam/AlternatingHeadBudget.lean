module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.AlternatingOrbitHeads
public import Theory.Representation.BinaryAlternatingSixModels.PairedHeads
public import CFSG.Quasithin.ChapterB.Section02.Thompson.InternalAction

/-!
# Paired natural-head displacement in the original alternating amalgam

The two original fixed-line orbit subgroups have inequivalent natural A₆
quotients under a single component marking. Embed them in the whole omega
module and add their fixed-codimension contributions, including when the
orbit subgroups intersect. An elementary actor with nontrivial component
image then exceeds the near-maximum displacement bound.

The actual consumer compares that strict inequality with B.2.4 on the
original Sylow group. Every near-maximum elementary subgroup contained in
the selected component lies in its literal two-core. The kernel equality
comes from the original relative-centralizer and prime-to-three residual
hypotheses, without replacing the component two-residual by its two-core.

The component and ordinary A₆ quotient are still selected case hypotheses.
Outer actors, Thompson normality, model selection and the other 13.4.7
branches remain to be discharged. All preceding Chapter 12 and 13.3 inputs
retain their original scope. Source: Aschbacher--Smith 13.4.7(1iv), p.901.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Theory.SpecificGroups.SymmetricSix BinaryDuadModule BinaryAlternatingSix
open Representation Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- Both original natural quotients contribute to movement on the whole
omega module, under the same actual component and parabolic marking. -/
theorem original_pair_alternating_paired_budget
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    original_pair_alternating_heads h₀ h structural D m hTA hTB eA eB hne hout
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

/-- A near-maximum elementary subgroup lying inside the original alternating
component is contained in its two-core. Outer actors remain a separate case. -/
theorem original_pair_alternating_inner_near_maximum_le_core
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃* A6)
    (E : Subgroup G) (hE : E ∈ ChapterB.thompsonFamily (T : Subgroup G) 1)
    (hEC : E ≤ K.map (A ⊔ B).subtype) :
    E ≤ (K.map (A ⊔ B).subtype).pCoreIn 2 := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  have hUX : U ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hred := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : (U.subgroupOf X).Normal := hred.normal
  let : IsElementaryAbelian 2 (U.subgroupOf X) := hred.elementary
  have hUS : U ≤ (T : Subgroup G) := by
    have hi := (IsElementaryAbelian.isPGroup 2 (U.subgroupOf X)).le_sylow_of_normal
      (T.subtype hTX)
    intro u hu
    exact hi (show (⟨u,hUX hu⟩ : X) ∈ U.subgroupOf X from hu)
  obtain ⟨he,e,_,hbudget⟩ := original_pair_alternating_paired_budget h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := he
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hcore := original_pair_component_action_kernel h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB hres K hK
  have hc : (centralizer (U : Set G)).subgroupOf C = pCore 2 C := by
    apply map_injective C.subtype_injective
    rw [subgroupOf_map_subtype,inf_comm]
    exact hcore
  have hk : f.ker = (centralizer (U : Set G)).subgroupOf C := by
    rw [hc,MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hu := ChapterB.near_maximum_internal_action_codimension (T : Subgroup G) U C E
    hUS ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X)) hEC hE f hk
  let := hE.2.1
  let : IsElementaryAbelian 2 (E.subgroupOf C) := IsElementaryAbelian.subgroupOf hEC
  let : IsElementaryAbelian 2 ((E.subgroupOf C).map f) := IsElementaryAbelian.map f
  have hz : (E.subgroupOf C).map f = ⊥ := by
    by_contra hn
    have hl := (hbudget (E.subgroupOf C)).2 ⟨hn,inferInstance⟩
    exact (not_lt_of_ge hu) hl
  have hi := (map_eq_bot_iff (E.subgroupOf C)).mp hz
  rw [hk,hc] at hi
  intro x hx
  exact mem_map_of_mem C.subtype (hi (show (⟨x,hEC hx⟩ : C) ∈ E.subgroupOf C from hx))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
