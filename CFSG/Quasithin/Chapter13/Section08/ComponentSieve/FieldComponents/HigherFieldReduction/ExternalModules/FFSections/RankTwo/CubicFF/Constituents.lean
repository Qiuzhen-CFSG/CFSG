module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.ActionSieve
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved.NoFF
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.Quotient

/-!
# Faithful natural constituents for the external cubic action

Let K be the normal odd-degree PSL₃ component and X the normal cubic group.
Every quadratic offender centralizes X: otherwise its rank is one and its
fixed codimension is half the ambient dimension, which exceeds one by the
commuting S₃ coordinates and the nontrivial K-action.

For a minimal best offender A centralizing X, the full B.1.5(3) implication
stabilizes every Irr⁺ section. The group K A has generalized Fitting subgroup
K and trivial centralizer of K. Consequently its literal action on I/C_I(K)
is faithful and satisfies the hypotheses of the complete B.4.2 implication.
The rank-two action sieve gives natural or binary dual-natural coordinates
under the original component marking, dimension 3n, and ratio 1/2.

These are constituent results. The cubic-pair codimension and equality
arguments, and the removal of the central kernel C_I(K), are separate steps
needed for the intrinsic no-strong and full moved-module theorems.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.5(3),
B.4.2 and F.9.18(6), used in 13.8.20(a), printed pp.954–955.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups ENNReal
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K A : Subgroup D) [K.Normal]

/-- The actual subspace I with its action of the generated group K A. -/
def constituentUpper (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hA : A ≤ subspaceStabilizer ρ I) :
    Subrepresentation (ρ.comp (K ⊔ A).subtype) :=
  ⟨I, fun g _ hv => (sup_le hI hA g.property _).2 hv⟩

/-- The K-fixed space, invariant under K A by normality of K. -/
def constituentCentral : Subrepresentation (ρ.comp (K ⊔ A).subtype) :=
  ⟨fixedSpace ρ K, fun g _ hv =>
    (fixedSpace_stable_of_normal ρ K (mem_top (g : D)) _).2 hv⟩

/-- The literal K A action on I/C_I(K); the central kernel is retained. -/
def constituentAction (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hA : A ≤ subspaceStabilizer ρ I) :
    Representation (ZMod 2) (K ⊔ A : Subgroup D) (centralQuotient ρ K I) :=
  sectionRepresentation (ρ.comp (K ⊔ A).subtype)
    (constituentCentral ρ K A) (constituentUpper ρ K A I hI hA)

omit [Finite D] [Finite V] in
/-- Restriction to the actual copy of K agrees with the original central quotient action. -/
theorem constituentAction_component (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) (hA : A ≤ subspaceStabilizer ρ I) :
    (constituentAction ρ K A I hI hA).comp (K.subgroupOf (K ⊔ A)).subtype =
      (centralQuotientRepresentation ρ K I hI).comp
        (subgroupOfEquivOfLe (show K ≤ K ⊔ A from le_sup_left)).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

omit [Finite D] [Finite V] in
/-- A self-centralizing quasisimple component makes every noncentral Irr⁺ section faithful. -/
theorem faithful_constituent [IsQuasisimple K]
    (hcent : centralizer ((K.subgroupOf (K ⊔ A)) : Set (K ⊔ A : Subgroup D)) = ⊥)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hA : A ≤ subspaceStabilizer ρ I) :
    Function.Injective (constituentAction ρ K A I hI.choose hA) := by
  let E := K ⊔ A
  let L := K.subgroupOf E
  let σ := constituentAction ρ K A I hI.choose hA
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).symm
  have hn : ¬ ∀ l ∈ L, ∀ v, σ l v = v := by
    intro ht
    apply hI.not_le_fixedSpace ρ
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ K I hI.choose
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,v,hv,rfl⟩
    exact (sectionRepresentation_trivial_iff (ρ.comp E.subtype)
      (constituentCentral ρ K A) (constituentUpper ρ K A I hI.choose hA)
      ⟨k,mem_sup_left hk⟩).mp (ht ⟨k,mem_sup_left hk⟩ hk) v hv
  have hk : (actionHom σ).ker = ⊥ := by
    apply bot_unique
    rw [← hcent]
    exact CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.action_kernel_le_centralizer σ L
      (CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.central_kernel_of_quasisimple σ L hn)
  intro a b hab
  apply (MonoidHom.ker_eq_bot_iff (actionHom σ)).mp hk
  exact imageRepresentation_injective σ hab

local instance (I : Submodule (ZMod 2) V) : Finite (centralQuotient ρ K I) :=
  Finite.of_surjective _ (Submodule.mkQ_surjective ((fixedSpace ρ K).comap I.subtype))

/-- The generated actor on the literal central quotient satisfies all B.4 hypotheses and is FF. -/
theorem constituent_b4 [IsQuasisimple K] {𝒦 : GroupClass.{u}}
    (hS : IsSQTK 𝒦 D) (hbest : IsBestOffender ρ A)
    (hfit : generalizedFitting (K ⊔ A : Subgroup D) = K.subgroupOf (K ⊔ A))
    (hcent : centralizer ((K.subgroupOf (K ⊔ A)) : Set (K ⊔ A : Subgroup D)) = ⊥)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hA : A ≤ subspaceStabilizer ρ I) :
    B4Hypotheses 𝒦 (constituentAction ρ K A I hI.choose hA) ∧
      IsFFModule (constituentAction ρ K A I hI.choose hA) := by
  let E := K ⊔ A
  let L := K.subgroupOf E
  let A₀ := A.subgroupOf E
  let σ := constituentAction ρ K A I hI.choose hA
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv
    (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).symm
  have hirr : IsIrreducible (σ.comp L.subtype) := by
    rw [constituentAction_component]
    exact (irreducible_comp_surjective_iff _
      (subgroupOfEquivOfLe (show K ≤ E from le_sup_left)).surjective _).mpr hI.choose_spec.2
  have hA₀ := hbest.subgroupOf ρ (show A ≤ E from le_sup_right)
  have hr : rank A₀ = rank A := by
    rw [← rank_map_injective E.subtype E.subtype_injective A₀]
    exact congrArg rank (map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right))
  have hcod : fixedCodim (ρ.comp E.subtype) A₀ = fixedCodim ρ A := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right)]
  refine ⟨{
    sqtk := hS.subgroup E
    faithful := faithful_constituent ρ K A hcent I hI hA
    quasisimple := by rw [hfit]; infer_instance
    irreducible := by rw [hfit]; exact hirr }, A₀, hA₀.1, ?_⟩
  exact (fixedCodim_section_le (ρ.comp E.subtype) (constituentCentral ρ K A)
    (constituentUpper ρ K A I hI.choose hA) A₀).trans (by
      rw [hcod, hr]
      exact (hbest.isOffender ρ).2)

variable {F : Type} [Field F] [Finite F] [CharP F 2]
  [Algebra (ZMod 2) F] {n : ℕ}

omit [Finite D] [K.Normal] [CharP F 2] [Algebra (ZMod 2) F] in
/-- The supplied odd-degree projective marking proves that the component has trivial center. -/
theorem component_center (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (e : K ≃* PSL(3,F)) : center K = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro k hk
  have hz := (centerCongr e ⟨k,hk⟩).property
  change e k ∈ center PSL(3,F) at hz
  rw [projectiveThree_center_eq_bot ho hF, mem_bot] at hz
  exact mem_bot.mpr (e.injective (hz.trans e.map_one.symm))

omit [CharP F 2] [Algebra (ZMod 2) F] in
/-- The common cubic centralizer bound discharges the generated actor hypotheses. -/
theorem centralizing_constituent_b4 [IsQuasisimple K] {𝒦 : GroupClass.{u}}
    (hS : IsSQTK 𝒦 D) (hbest : IsBestOffender ρ A)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hKX : K ≤ centralizer (X : Set D)) (hAX : A ≤ centralizer (X : Set D))
    (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hA : A ≤ subspaceStabilizer ρ I) :
    B4Hypotheses 𝒦 (constituentAction ρ K A I hI.choose hA) ∧
      IsFFModule (constituentAction ρ K A I hI.choose hA) := by
  have hfit := generated_fitting K X hx hc hKX hbest.1 hAX
  let eL := (subgroupOfEquivOfLe (show K ≤ K ⊔ A from le_sup_left)).trans e
  exact constituent_b4 ρ K A hS hbest hfit
    (selfcentral_of_fitting _ hfit (component_center (K.subgroupOf (K ⊔ A)) ho hF eL)) I hI hA

omit [CharP F 2] in
/-- The full B.4.2 implication recognizes the original marking and retains the exact ratio. -/
theorem centralizing_constituent_natural [IsQuasisimple K] {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) (hS : IsSQTK 𝒦 D) (hbest : IsBestOffender ρ A)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hKX : K ≤ centralizer (X : Set D)) (hAX : A ≤ centralizer (X : Set D))
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hA : A ≤ subspaceStabilizer ρ I) :
    IsProjectiveNaturalOrDual ho hF
      ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom) ∧
      quadraticRatio (constituentAction ρ K A I hI.choose hA) = 1 / 2 := by
  obtain ⟨hb,hff⟩ := centralizing_constituent_b4 ρ K A hS hbest X hx hc hKX hAX ho hF e I hI hA
  have hfit := generated_fitting K X hx hc hKX hbest.1 hAX
  let a : generalizedFitting (K ⊔ A : Subgroup D) ≃* K :=
    (MulEquiv.subgroupCongr hfit).trans (subgroupOfEquivOfLe le_sup_left)
  let σ := constituentAction ρ K A I hI.choose hA
  constructor
  · apply naturalOrDual_of_ff_coordinates σ hB42 hb hff hn ho hF
      (centralQuotientRepresentation ρ K I hI.choose) e a (LinearEquiv.refl _ _)
    intro g v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl
  · obtain ⟨_,_,_,_,hq⟩ := natural_of_ff σ hB42 hb hff hn ho hF (a.trans e)
    exact hq

/-- All hypotheses of the complete B.1.5(3) implication hold for this component and offender. -/
theorem minimal_stabilizes [IsQuasisimple K]
    (hInv : FullIrrInvariance.{u,v}) (hf : Function.Injective ρ)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hAX : A ≤ centralizer (X : Set D)) (hA : IsMinimalBestOffender ρ A)
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I) :
    A ≤ subspaceStabilizer ρ I := by
  obtain ⟨hr,hchief⟩ := quasisimple_stabilization_hypotheses K
  have hK : K ≠ ⊥ := by
    intro he
    exact hI.not_le_fixedSpace ρ (by rw [he, fixedSpace_bot]; exact le_top)
  exact hInv D V ρ hf A K hA hK hr
    (component_commutator_of_centralizes_cubic K X hx hc hA.1.1 hAX) hchief I hI

omit [Finite D] [Finite V] [K.Normal] [CharP F 2] in
/-- Both natural orientations have binary dimension 3n under the given field cardinality. -/
theorem naturalOrDual_finrank (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    (σ : Representation (ZMod 2) PSL(3,F) V)
    (hσ : IsProjectiveNaturalOrDual ho hF σ) : Module.finrank (ZMod 2) V = 3 * n := by
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  have hv : Module.finrank (ZMod 2) (Fin 3 → F) = 3 * n := by
    simp only [Module.finrank_pi_fintype, hd, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rcases hσ with ⟨a,_⟩ | ⟨a,_⟩
  · exact a.finrank_eq.trans hv
  · exact a.finrank_eq.trans (Subspace.dual_finrank_eq.trans hv)

omit [Finite V] [K.Normal] in
/-- Ratio 1/2 gives a lower bound for every quadratic elementary actor. -/
theorem rank_le_twice_codim (hq : quadraticRatio ρ = 1 / 2)
    (hA : IsElementaryTwo A) (hquad : IsQuadratic ρ A) :
    rank A ≤ 2 * fixedCodim ρ A := by
  have h : (1 / 2 : ℝ≥0∞) ≤ actionRatio ρ A := by
    rw [← hq]
    exact iInf_le_of_le A (iInf_le _ ⟨hA,hquad⟩)
  have hr : (rank A : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hA.rank_pos)
  have hh : (1 / 2 : ℝ≥0∞) * rank A ≤ fixedCodim ρ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hr) (Or.inl (by simp))).mp h
  have hnat : (rank A : ℝ≥0∞) ≤ 2 * fixedCodim ρ A := by
    calc
      _ = (2 : ℝ≥0∞) * (1 / 2 * rank A) := by
        norm_num [div_eq_mul_inv, ← mul_assoc, ENNReal.mul_inv_cancel]
      _ ≤ _ := mul_le_mul' le_rfl hh
  exact_mod_cast hnat

omit [K.Normal] in
/-- The rank-one calculation excludes every quadratic offender moving the cubic group. -/
theorem quadratic_offender_centralizes
    (X : Subgroup D) [X.Normal] (hx : Nat.card X = 3)
    (hf : Function.Injective ρ)
    (s : InvertedCubicTensor.S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (hn : ¬ ∀ k ∈ K, ∀ v, ρ k v = v)
    (hA : IsOffender ρ A) (hq : IsQuadratic ρ A) :
    A ≤ centralizer (X : Set D) := by
  by_contra hAX
  have hfree := InvertedCubicTensor.ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hd := cubic_dimension_gt_two K ρ s hs hfree hn
  obtain ⟨hr,hcod⟩ := normalThree_quadratic_rank_fixedCodim ρ hf X inferInstance hx hg A hA.1 hq hAX
  have := hA.2
  omega

omit [Finite D] [Finite V] [K.Normal] in
/-- A faithful action of a quasisimple component cannot be trivial. -/
theorem quasisimple_noncentral [IsQuasisimple K] (hf : Function.Injective ρ) :
    ¬ ∀ k ∈ K, ∀ v, ρ k v = v := by
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center K))
  obtain ⟨k,hk⟩ := exists_ne (1 : K)
  intro ht
  apply hk
  apply Subtype.ext
  apply hf
  ext v
  simpa only [Subgroup.coe_one, map_one, Module.End.one_apply] using ht k k.property v

omit [Finite V] in
/-- The constituent ratio controls the rank of the same actual ambient offender. -/
theorem constituent_half_bound (hbest : IsBestOffender ρ A)
    (hquad : IsQuadratic ρ A)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (hA : A ≤ subspaceStabilizer ρ I)
    (hratio : quadraticRatio (constituentAction ρ K A I hI hA) = 1 / 2) :
    rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI hA) (A.subgroupOf (K ⊔ A)) := by
  let E := K ⊔ A
  let A₀ := A.subgroupOf E
  have helem := (hbest.subgroupOf ρ (show A ≤ E from le_sup_right)).1
  have hq : IsQuadratic (ρ.comp E.subtype) A₀ :=
    fun a ha b hb v => hquad a ha b hb v
  have hh := rank_le_twice_codim (constituentAction ρ K A I hI hA) A₀ hratio helem
    (quadratic_section (ρ.comp E.subtype) (constituentCentral ρ K A)
      (constituentUpper ρ K A I hI hA) hq)
  have hr : rank A₀ = rank A := by
    rw [← rank_map_injective E.subtype E.subtype_injective A₀]
    exact congrArg rank (map_subgroupOf_eq_of_le (show A ≤ E from le_sup_right))
  rwa [hr] at hh

omit [CharP F 2] in
/-- Select a stabilized natural central quotient and retain its exact dimension and codimension bound. -/
theorem exists_recognized_constituent [IsQuasisimple K] {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
    (hS : IsSQTK 𝒦 D) (hf : Function.Injective ρ)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hKX : K ≤ centralizer (X : Set D)) (hAX : A ≤ centralizer (X : Set D))
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
      (hAI : A ≤ subspaceStabilizer ρ I),
      IsProjectiveNaturalOrDual ho hF
        ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom) ∧
      quadraticRatio (constituentAction ρ K A I hI.choose hAI) = 1 / 2 ∧
      rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
        (A.subgroupOf (K ⊔ A)) ∧
      Module.finrank (ZMod 2) (centralQuotient ρ K I) = 3 * n := by
  have hK : K ≠ ⊥ := by
    intro he
    apply quasisimple_noncentral ρ K hf
    simp [he]
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf K hK
  have hAI := minimal_stabilizes ρ K A hInv hf X hx hc hAX hA I hI
  obtain ⟨hnat,hratio⟩ := centralizing_constituent_natural ρ K A hB42 hS hA.1 X hx hc
    hKX hAX hn ho hF e I hI hAI
  refine ⟨I,hI,hAI,hnat,hratio,
    constituent_half_bound ρ K A hA.1 hquad I hI.choose hAI hratio, ?_⟩
  exact naturalOrDual_finrank ho hF _ hnat

omit [Finite D] [K.Normal] in
/-- The marked alternating subgroup lies in the centralizer of the component. -/
theorem marked_component_centralizes_cubic
    (X : Subgroup D) (s : InvertedCubicTensor.S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X) :
    K ≤ centralizer (X : Set D) := by
  intro k hk x hx
  rw [← hmark] at hx
  obtain ⟨g,_,rfl⟩ := hx
  exact (hs ⟨k,hk⟩ g).symm.eq

omit [CharP F 2] in
/-- The structural cubic hypotheses produce the recognized constituent for every quadratic minimal best offender. -/
theorem quadratic_minimal_constituent [IsQuasisimple K] {𝒦 : GroupClass.{u}}
    (hB42 : FullB42.{u,v} 𝒦) (hInv : FullIrrInvariance.{u,v})
    (hS : IsSQTK 𝒦 D) (hf : Function.Injective ρ)
    (X : Subgroup D) [X.Normal] (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : InvertedCubicTensor.S₃ →* D)
    (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    A ≤ centralizer (X : Set D) ∧
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
      (hAI : A ≤ subspaceStabilizer ρ I),
      IsProjectiveNaturalOrDual ho hF
        ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom) ∧
      quadraticRatio (constituentAction ρ K A I hI.choose hAI) = 1 / 2 ∧
      rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
        (A.subgroupOf (K ⊔ A)) ∧
      Module.finrank (ZMod 2) (centralQuotient ρ K I) = 3 * n := by
  have hAX := quadratic_offender_centralizes ρ K A X hx hf s hs hmark hg
    (quasisimple_noncentral ρ K hf) (hA.1.isOffender ρ) hquad
  exact ⟨hAX, exists_recognized_constituent ρ K A hB42 hInv hS hf X hx hc
    (marked_component_centralizes_cubic K X s hs hmark) hAX hn ho hF e hA hquad⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.CubicFF
