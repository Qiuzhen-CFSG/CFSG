module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Homogeneous
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Sections

/-!
# The faithful irreducible source quotient

The maximal proper source submodule has a faithful irreducible quotient
for the exchanged actor. In the central branch its kernel is exactly the
full fixed space of the normal component orbit. The homogeneous section
and both generating orbit spans are retained. We also identify the two
conjugation conventions on the actual exchanged component, and transport
cross-factor fixation through the literal bottom quotient.

Source: Aschbacher–Smith, 13.8.16(1), printed p.952.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

/-- Both literal cross-factor inequalities descend to a proper quotient. -/
theorem crossFactorQuotient_of_crossFixation
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U] [Nontrivial U]
    (ρ : Representation (ZMod 2) D U) (A B : Subgroup D)
    (ha : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B)
    (hb : subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A) :
    HasCrossFactorQuotient ρ A B := by
  refine ⟨⊥, bot_ne_top, ?_, ?_⟩
  all_goals
    rw [← show ((⊤ : Submodule (ZMod 2) U).map
        (⊥ : Subrepresentation ρ).toSubmodule.mkQ) = ⊤ by
      rw [Submodule.map_top, Submodule.range_mkQ]]
    rw [← commutator_map ρ (⊥ : Subrepresentation ρ).quotientRepresentation
      (⊥ : Subrepresentation ρ).toSubmodule.mkQ
      (fun g u => ((⊥ : Subrepresentation ρ).quotientRepresentation_mk g u).symm)]
  · exact quotient_seed_fixed ρ ⊥ _ B ha
  · exact quotient_seed_fixed ρ ⊥ _ A hb

/-- On a noncentral irreducible quotient, a central kernel is the entire
fixed space of the normal component orbit. -/
private theorem central_kernel_eq_fixedSpace
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N : Subgroup D) [N.Normal]
    (W : Subrepresentation ρ) [W.quotientRepresentation.IsIrreducible]
    (hfull : subspaceCommutator W.quotientRepresentation ⊤ N = ⊤)
    (hc : W.toSubmodule ≤ fixedSpace ρ N) : W.toSubmodule = fixedSpace ρ N := by
  let σ := W.quotientRepresentation
  let : Nontrivial (U ⧸ W.toSubmodule) := Subrepresentation.irreducible_module_nontrivial σ
  let C : Subrepresentation σ := {
    toSubmodule := fixedSpace σ N
    apply_mem_toSubmodule := by
      intro g v hv
      exact ((fixedSpace_stable_of_normal σ N (mem_top g)) v).2 hv }
  have hC : C = ⊥ := by
    rcases IsSimpleOrder.eq_bot_or_eq_top C with h | h
    · exact h
    · have hh : subspaceCommutator σ ⊤ N = ⊥ := by
        apply (subspaceCommutator_eq_bot_iff σ ⊤ N).mpr
        exact (congrArg Subrepresentation.toSubmodule h).ge
      have hn : (⊤ : Submodule (ZMod 2) (U ⧸ W.toSubmodule)) ≠ ⊥ := top_ne_bot
      exact (hn (hfull.symm.trans hh)).elim
  apply le_antisymm hc
  intro u hu
  apply (Submodule.Quotient.mk_eq_zero W.toSubmodule).mp
  have hq : W.toSubmodule.mkQ u ∈ C := by
    intro n
    change W.quotientRepresentation (n : D) (W.toSubmodule.mkQ u) = W.toSubmodule.mkQ u
    rw [W.quotientRepresentation_mk]
    exact congrArg W.toSubmodule.mkQ (hu n)
  rw [hC] at hq
  exact hq

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving

omit hgen in
/-- The two right-conjugation conventions agree on the literal exchanged
component, because its T-normalizer has index two. -/
theorem source_star_inverse_conjugate {t : G} (ht : t ∈ T) :
    let hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
    let ts := QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩
    (Source.starImage H K).conjBy ts⁻¹ = Source.starImage H (K.conjBy t) := by
  intro hTH ts
  have hi := Original.moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  have hsq := (normalizer (K.subgroupOf H : Set H)).sq_mem_of_index_two hi (⟨t,hTH ht⟩ : H)
  rw [← subgroupOf_normalizer_eq hKH] at hsq
  change t ^ 2 ∈ normalizer (K : Set G) at hsq
  have hret : (K.conjBy t).conjBy t = K := by
    rw [← conjBy_mul]
    exact mem_normalizer_iff_map_conj_eq.mp (by simpa only [pow_two] using hsq)
  have he : K.conjBy t⁻¹ = K.conjBy t := by
    have hh := congrArg (fun J : Subgroup G => J.conjBy t⁻¹) hret
    simpa only [conjBy_inv] using hh.symm
  have hq : ts⁻¹ = QuotientGroup.mk' (pCore 2 H) ⟨t⁻¹,hTH (T.inv_mem ht)⟩ := by
    exact (map_inv (QuotientGroup.mk' (pCore 2 H)) (⟨t,hTH ht⟩ : H)).symm
  rw [hq]
  change (Source.starImage H K).map
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨t⁻¹,hTH (T.inv_mem ht)⟩)).toMonoidHom = _
  rw [starImage_conjBy H K hKH (hTH (T.inv_mem ht)),he]

/-- The central branch is the literal quotient by the entire fixed space,
with a faithful irreducible quotient and a homogeneous generating section. -/
theorem source_central_kernel_dichotomy {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      W.quotientRepresentation.IsIrreducible ∧
      Function.Injective W.quotientRepresentation ∧
      (sourceSeedSpace H V₃ V₁).map W.toSubmodule.mkQ ≠ ⊥ ∧
      ((IsFFModule (imageRepresentation W.toRepresentation) ∧
        IsFFModule (imageRepresentation W.quotientRepresentation)) ∨
       (W.toSubmodule = fixedSpace ρ
          (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) ∧
        ∃ I, Homogeneous.IsIrrPlusWith ρ
            (Source.starImage H (conjugateSpanBy K (T : Subgroup G)))
            (Source.starImage H T) I ∧
          seedSpan ρ I = ⊤ ∧ Homogeneous.orbitSpan ρ ⊤ I = ⊤ ∧
          Homogeneous.orbitSpan ρ (Source.starImage H T) I = ⊤)) := by
  obtain ⟨W,hW,hmax,hseed,halt⟩ := source_homogeneous_section_dichotomy
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ρ hρ
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmoving
  obtain ⟨F,hF,hfin,hchar,a,_,_,ha,hS⟩ := exists_source_exchangedActor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  have hfull := Original.moved_eq_top d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving hn hmodel hgen ρ hρ
  have havoid : ¬ subspaceCommutator ρ ⊤ a.orbit ≤ W.toSubmodule := by
    rw [ha,hfull]
    intro hh
    exact hW (Subrepresentation.toSubmodule_injective (top_unique hh))
  let : W.quotientRepresentation.IsIrreducible :=
    FFFactors.maximal_component_section_irreducible ρ W a.orbit (ha.symm ▸ hfull) havoid (by
      intro Y hWY hY
      apply hmax Y hWY
      intro he
      exact hY (he ▸ le_top))
  let : Nontrivial ((SourceSpace H V₃ V₁) ⧸ W.toSubmodule) :=
    Subrepresentation.irreducible_module_nontrivial W.quotientRepresentation
  have hqfull : subspaceCommutator W.quotientRepresentation ⊤ a.orbit = ⊤ := by
    rw [ha]
    have hh := quotient_seed_commutator ρ W ⊤ _ hfull
    simpa only [Submodule.map_top,Submodule.range_mkQ] using hh
  have hfaith : Function.Injective W.quotientRepresentation :=
    a.faithful_of_noncentral W.quotientRepresentation (by
      intro hh
      have hz : subspaceCommutator W.quotientRepresentation ⊤ a.orbit = ⊥ :=
        (subspaceCommutator_eq_bot_iff _ _ _).mpr (fun v _ g => hh g g.property v)
      have hn : (⊤ : Submodule (ZMod 2) ((SourceSpace H V₃ V₁) ⧸ W.toSubmodule)) ≠ ⊥ := top_ne_bot
      exact hn (hqfull.symm.trans hz))
  refine ⟨W,hW,inferInstance,hfaith,hseed,?_⟩
  rcases halt with hff | ⟨hc,I,hI,hspan,hG,hT⟩
  · exact Or.inl hff
  · let : a.orbit.Normal := a.orbit_normal
    have hce : W.toSubmodule = fixedSpace ρ a.orbit :=
      central_kernel_eq_fixedSpace ρ a.orbit W hqfull (by
        rw [ha]
        exact (subspaceCommutator_eq_bot_iff ρ _ _).mp hc)
    exact Or.inr ⟨ha ▸ hce,I,hI,hspan,hG,hT⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
