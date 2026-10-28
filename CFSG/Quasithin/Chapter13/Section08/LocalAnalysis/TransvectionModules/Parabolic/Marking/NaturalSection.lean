module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.NaturalSection.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic

/-!
# The literal natural section for 13.8.6

The commutator image is all of U_H/V₁ in either six-letter model. This does
not assume that U_H itself is commutator-generated. The fixed space is the
kernel of the natural projection, giving an equivariant identification of
Ũ_K/C_{Ũ_K}(K). The intrinsic K/O₂(K) action is checked on representatives
through the relative C-component quotient equivalence.

The application retains 13.7.6(3) as an explicit universal earlier-theorem
input at the fixed standing source configuration. It constructs that theorem's
natural-section premise and specializes its degree alternatives; it does not
prove the earlier theorem or the global standing hypotheses of §13.8.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6(3),
printed pp.938–939, and the first paragraph of 13.8.6, printed p.948.
-/

@[expose] public section
open Module Representation Representation.BinaryOffender BinaryPermutation Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.NaturalSection
open scoped IsMulCommutative
open TransvectionRecognition
open TransvectionRecognition.Component

private theorem commutator_eq_top {A B E F : Type*} [Group A] [Group B]
    [AddCommGroup E] [Module (ZMod 2) E] [AddCommGroup F] [Module (ZMod 2) F]
    (ρ : Representation (ZMod 2) A E) (σ : Representation (ZMod 2) B F)
    (K : Subgroup A) (eK : K ≃* B) (e : E ≃ₗ[ZMod 2] F)
    (he : ∀ (k : K) v, e (ρ k v) = σ (eK k) (e v))
    (hg : Coinvariants.ker σ = ⊤) : subspaceCommutator ρ ⊤ K = ⊤ := by
  let C := subspaceCommutator ρ ⊤ K
  have h : Coinvariants.ker σ ≤ C.comap e.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change e.symm (σ a v - v) ∈ C
    have hh : e.symm (σ a v - v) = ρ (eK.symm a) (e.symm v) - e.symm v := by
      apply e.injective
      rw [e.apply_symm_apply, map_sub, he, eK.apply_symm_apply, e.apply_symm_apply]
    rw [hh]
    exact Submodule.subset_span ⟨eK.symm a, (eK.symm a).property,
      e.symm v, Submodule.mem_top, rfl⟩
  apply top_unique
  intro v _
  have hh := h (show e v ∈ Coinvariants.ker σ from hg.symm ▸ Submodule.mem_top)
  change e.symm (e v) ∈ C at hh
  simpa only [e.symm_apply_apply] using hh

variable {G : Type*} [Group G]
    {H V₃ V₁ : Subgroup G}
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- Generation of the literal image, without assuming generation of U_H. -/
theorem commutatorImage_eq_top
    (K : Subgroup G) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) A E)
    (eK : Source.starImage H K ≃* A)
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ (k : Source.starImage H K) v, e (ρ k v) = σ (eK k) (e v))
    (hg : Coinvariants.ker σ = ⊤) : commutatorImage H V₃ V₁ K = ⊤ := by
  change sectionImage H V₃ V₁ ⁅Source.UH H V₃, K⁆ = ⊤
  rw [commutator_image ρ hρ K hKH]
  exact commutator_eq_top ρ σ _ eK e he hg

/-- Fixed vectors in any literal subspace are precisely the kernel of a
compatible model projection whose kernel is the model fixed space. -/
theorem fixedInCommutator_eq_kernel
    (K : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    {A E F : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) A E)
    (eK : Source.starImage H K ≃* A)
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ (k : Source.starImage H K) v, e (ρ k v) = σ (eK k) (e v))
    (p : E →ₗ[ZMod 2] F) (hp : invariants σ = p.ker) :
    fixedInCommutator H V₃ V₁ ρ K =
      (p.comp (e.toLinearMap.comp (commutatorImage H V₃ V₁ K).subtype)).ker := by
  ext v
  change (∀ k : Source.starImage H K, ρ k v.val = v.val) ↔ p (e v.val) = 0
  rw [← LinearMap.mem_ker, ← hp]
  constructor
  · intro hv a
    obtain ⟨k, rfl⟩ := eK.surjective a
    rw [← he, hv k]
  · intro hv k
    apply e.injective
    rw [he]
    exact hv (eK k)

/-- A natural model for Ũ_K/C_{Ũ_K}(K), with the intrinsic quotient's
representatives transported through the actual component-star equivalence. -/
theorem section_model_of_projection [Finite G]
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    {A E F : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) A E) (τ : Representation (ZMod 2) A F)
    (eK : Source.starImage H K ≃* A)
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ (k : Source.starImage H K) v, e (ρ k v) = σ (eK k) (e v))
    (hg : Coinvariants.ker σ = ⊤)
    (p : E →ₗ[ZMod 2] F) (hps : Function.Surjective p)
    (hpk : invariants σ = p.ker) (hpe : ∀ a v, p (σ a v) = τ a (p v)) :
    HasSectionModel H V₃ V₁ ρ K hKH τ
      ((Components.componentStarEquiv H K hKH hK).trans eK) := by
  let I := commutatorImage H V₃ V₁ K
  have hI : I = ⊤ := commutatorImage_eq_top K hKH ρ hρ σ eK e he hg
  let f := p.comp (e.toLinearMap.comp I.subtype)
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v, rfl⟩ := hps w
    refine ⟨⟨e.symm v, hI.symm ▸ Submodule.mem_top⟩, ?_⟩
    change p (e (e.symm v)) = p v
    rw [e.apply_symm_apply]
  have hk : fixedInCommutator H V₃ V₁ ρ K = f.ker :=
    fixedInCommutator_eq_kernel K ρ σ eK e he p hpk
  let E := (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hf)
  refine ⟨commutatorImage_invariant K hKH ρ hρ, E, ?_⟩
  intro k u
  change p (e (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u.val)) = _
  let kstar := Components.componentStarEquiv H K hKH hK (QuotientGroup.mk' (pCore 2 K) k)
  have hks : (kstar : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hKH k) :=
    Components.componentStarEquiv_mk H K hKH hK k
  rw [← hks, he, hpe]
  rfl


/-- In dimension four the literal section is the natural module itself. -/
theorem natural_section_model [Finite G]
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      e (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (e v)) :
    HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6))
      ((Components.componentStarEquiv H K hKH hK).trans eK) := by
  apply section_model_of_projection K hKH hK ρ hρ _ _ eK e he natural_generated
    (LinearMap.id) (fun v => ⟨v, rfl⟩)
  · simpa only [LinearMap.ker_id] using natural_fixed_eq_bot
  · intro a v; rfl

/-- In dimension five the literal section is the natural quotient of the cover. -/
theorem cover_section_model [Finite G]
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      e (ρ k v) = alternatingCoreRepresentation (Fin 6) (eK k) (e v)) :
    HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6))
      ((Components.componentStarEquiv H K hKH hK).trans eK) :=
  section_model_of_projection K hKH hK ρ hρ _ _ eK e he
    ComponentSieve.SixAndG2.alternatingSix_core_generated
    (coreToNatural (Fin 6)) coreToNatural_surjective core_fixed_eq_kernel
    (fun a v => coreToNatural_equivariant a.val v)

/-- The fixed subspace of the literal commutator image vanishes in dimension four. -/
theorem natural_fixedInCommutator_eq_bot
    (K : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      e (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (e v)) :
    fixedInCommutator H V₃ V₁ ρ K = ⊥ := by
  rw [fixedInCommutator_eq_kernel K ρ _ eK e he LinearMap.id (by
    simpa only [LinearMap.ker_id] using natural_fixed_eq_bot)]
  apply LinearMap.ker_eq_bot.mpr
  exact e.injective.comp (commutatorImage H V₃ V₁ K).subtype_injective

/-- The fixed subspace of the literal commutator image in dimension five is
exactly the kernel of the canonical natural projection in the supplied coordinates. -/
theorem cover_fixedInCommutator_eq_kernel
    (K : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ (k : Source.starImage H K) v,
      e (ρ k v) = alternatingCoreRepresentation (Fin 6) (eK k) (e v)) :
    fixedInCommutator H V₃ V₁ ρ K =
      ((coreToNatural (Fin 6)).comp
        (e.toLinearMap.comp (commutatorImage H V₃ V₁ K).subtype)).ker :=
  fixedInCommutator_eq_kernel K ρ _ eK e he _ core_fixed_eq_kernel

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.NaturalSection

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.NaturalSection
open TransvectionRecognition TransvectionRecognition.Component
open scoped IsMulCommutative
variable {G : Type*} [Group G]

open scoped Pointwise

/-- A weight-four point marking of the actual V₂ image. Both alternatives
retain an equivariant identification of the literal U_H/V₁, so a coordinate
change also transports the component action. -/
def SixPointMarking
    (H K V₂ V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  ∃ eK : Source.starImage H K ≃* alternatingGroup (Fin 6),
    (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
      (∀ (k : Source.starImage H K) v,
        e (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (e v)) ∧
      (sectionImage H V₃ V₁ V₂).map e.toLinearMap =
        Submodule.span (ZMod 2) {coreToNatural (Fin 6) OrbitModels.point}) ∨
    (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
      (∀ (k : Source.starImage H K) v,
        e (ρ k v) = alternatingCoreRepresentation (Fin 6) (eK k) (e v)) ∧
      (sectionImage H V₃ V₁ V₂).map e.toLinearMap = OrbitModels.pointSpace)

/-- The used clauses of the universal earlier 13.7.6(3), at a fixed standing
configuration from Hypothesis 13.7.1 and Notations 13.2.1, 13.3.3 and 13.5.8.
This is an explicit theorem input, not an assertion that arbitrary subgroups
satisfy that standing configuration. It quantifies over every H in the genuine
family H_z, every relative C-component, every alternating degree, and every
conjugation-compatible action on the literal section.

The degree-seven alternative retains the actual quasisimple triple cover of A₆.
The unused two-chief-factor clause in (a) and the two flag coordinates in (b)
are omitted. The degree-six coordinates express the source's instruction to
apply the notation of B.3 to Ũ_H; they may differ from the input coordinates.
The antecedent uses the natural model of the commutator image modulo its fixed
space. Commutator generation of U_H is a conclusion.
-/
def Earlier1376 [Finite G] (L L₁ T G₁ M V₂ V₃ V₁ : Subgroup G) : Prop :=
  ∀ (H : Subgroup G), H ∈ Source.Hz L₁ T G₁ M →
    V₁ ≤ Source.UH H V₃ →
    ∀ [_hn : (V₁.subgroupOf (Source.UH H V₃)).Normal]
      [_ha : IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
      (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (K : Subgroup G) (hKH : K ≤ H), (K.subgroupOf H).IsCComponent →
      ∀ (n : ℕ), 5 ≤ n → ∀ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n),
      HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin n)) eK →
        Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ ∧ L₁ ≤ K ∧
        (H : Set G) = (K : Set G) * (T : Set G) ∧
        ((n = 6 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          SixPointMarking H K V₂ V₃ V₁ ρ) ∨
         (n = 7 ∧ SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)))

/-- Applicability of 13.7.6(3) in both cases of 13.8.6. The natural-section
premise is proved above, and the degree-seven alternative is eliminated only
after applying the universal earlier implication at degree six.

The product H=KT is also recovered from the earlier theorem, so this deduction
does not need to assume that additional hypothesis of 13.8.6. All global
standing hypotheses remain the responsibility of the theorem supplying `earlier`.
-/
theorem apply_earlier [Finite G]
    (L L₁ T G₁ M H K V₂ V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (earlier : Earlier1376 L L₁ T G₁ M V₂ V₃ V₁)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hV₁ : V₁ ≤ Source.UH H V₃)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (hmodel :
      (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6),
        ∀ (k : Source.starImage H K) v,
          e (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k) (e v)) ∨
      (∃ e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6),
        ∀ (k : Source.starImage H K) v,
          e (ρ k v) = alternatingCoreRepresentation (Fin 6) (eK k) (e v))) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ ∧ L₁ ≤ K ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      SixPointMarking H K V₂ V₃ V₁ ρ := by
  let e := (Components.componentStarEquiv H K hKH hK).trans eK
  have hsec : HasSectionModel H V₃ V₁ ρ K hKH
      (alternatingNaturalRepresentation (Fin 6)) e := by
    rcases hmodel with ⟨E, hE⟩ | ⟨E, hE⟩
    · exact natural_section_model K hKH hK ρ hρ eK E hE
    · exact cover_section_model K hKH hK ρ hρ eK E hE
  obtain ⟨hgen, hLK, hprod, halt⟩ := earlier H hH hV₁ ρ hρ K hKH hK 6 (by decide) e hsec
  rcases halt with ⟨_, hL, hm⟩ | ⟨h7, _⟩
  · exact ⟨hL, hgen, hLK, hprod, hm⟩
  · exact (by omega : False).elim

/-- A natural input module forces the natural alternative in the source point
marking. The explicit automorphism records the change from supplied coordinates. -/
theorem SixPointMarking.natural_coordinates
    {H K V₂ V₃ V₁ : Subgroup G}
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    {ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))}
    (hm : SixPointMarking H K V₂ V₃ V₁ ρ)
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6)) :
    ∃ (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
      (c : natural (Fin 6) ≃ₗ[ZMod 2] natural (Fin 6)),
      (∀ (k : Source.starImage H K) v,
        (e.trans c) (ρ k v) = alternatingNaturalRepresentation (Fin 6) (eK k)
          ((e.trans c) v)) ∧
      (sectionImage H V₃ V₁ V₂).map (e.trans c).toLinearMap =
        Submodule.span (ZMod 2) {coreToNatural (Fin 6) OrbitModels.point} := by
  obtain ⟨eK, hm⟩ := hm
  rcases hm with ⟨E, hE, hp⟩ | ⟨E, _, _⟩
  · refine ⟨eK, e.symm.trans E, ?_, ?_⟩
    · intro k v; simpa using hE k v
    · have heq : e.trans (e.symm.trans E) = E := by ext v; simp
      rw [heq]
      exact hp
  · have hdim := (e.symm.trans E).finrank_eq
    rw [finrank_natural_even (Fin 6) (by decide), finrank_core] at hdim
    norm_num at hdim

/-- A cover input module forces the cover alternative, retaining a genuine
weight-four vector rather than its ambiguous weight-two quotient representative. -/
theorem SixPointMarking.cover_coordinates
    {H K V₂ V₃ V₁ : Subgroup G}
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    {ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))}
    (hm : SixPointMarking H K V₂ V₃ V₁ ρ)
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6)) :
    ∃ (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
      (c : core (Fin 6) ≃ₗ[ZMod 2] core (Fin 6)),
      (∀ (k : Source.starImage H K) v,
        (e.trans c) (ρ k v) = alternatingCoreRepresentation (Fin 6) (eK k)
          ((e.trans c) v)) ∧
      (sectionImage H V₃ V₁ V₂).map (e.trans c).toLinearMap = OrbitModels.pointSpace := by
  obtain ⟨eK, hm⟩ := hm
  rcases hm with ⟨E, _, _⟩ | ⟨E, hE, hp⟩
  · have hdim := (e.symm.trans E).finrank_eq
    rw [finrank_core, finrank_natural_even (Fin 6) (by decide)] at hdim
    norm_num at hdim
  · refine ⟨eK, e.symm.trans E, ?_, ?_⟩
    · intro k v; simpa using hE k v
    · have heq : e.trans (e.symm.trans E) = E := by ext v; simp
      rw [heq]
      exact hp

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.NaturalSection
