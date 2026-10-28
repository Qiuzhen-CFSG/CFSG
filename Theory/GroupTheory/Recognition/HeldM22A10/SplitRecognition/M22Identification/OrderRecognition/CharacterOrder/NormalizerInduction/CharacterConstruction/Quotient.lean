module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Classes

/-!
# The actual alternating-six quotient of the normalizer

The complement supplied by local analysis identifies the quotient by the
actual E with A6. Composing this equivalence with the quotient map gives the
surjection used to inflate characters. On the marked involution centralizer,
its kernel is exactly the binary factor, so the original S4 actors embed in
this A6 quotient. No identification of the full normalizer action is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Lemma 6 and Section 6, pp.10–11.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- Membership in the actual E, on the given centralizer coordinates,
is precisely triviality of the actor coordinate. -/
public theorem normalizerCentralizer_mem_E (x : TwistedModel) :
    normalizerCentralizer D k x ∈
      (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) ↔ x.right = 1 := by
  constructor
  · rintro ⟨v, hv⟩
    have h : (SemidirectProduct.inl v : TwistedModel) = x :=
      CaseII.into_injective D k hv
    exact (congrArg SemidirectProduct.right h).symm
  · intro hx
    refine ⟨x.left, ?_⟩
    change CaseII.into D k (SemidirectProduct.inl x.left) = CaseII.into D k x
    congr 1
    exact SemidirectProduct.ext rfl hx.symm

variable (K : Subgroup (normalizer (CaseII.E D k : Set G)))
    (hK : ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K)
    (eK : K ≃* alternatingGroup (Fin 6))

/-- The genuine quotient map supplied by an actual A6 complement. -/
@[expose] public def normalizerQuotient :
    normalizer (CaseII.E D k : Set G) →* alternatingGroup (Fin 6) :=
  (hK.symm.QuotientMulEquiv.trans eK).toMonoidHom.comp
    (QuotientGroup.mk' ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))))

public theorem normalizerQuotient_surjective :
    Function.Surjective (normalizerQuotient D k K hK eK) :=
  (hK.symm.QuotientMulEquiv.trans eK).surjective.comp (QuotientGroup.mk'_surjective _)

public theorem normalizerQuotient_ker :
    (normalizerQuotient D k K hK eK).ker =
      (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  rw [normalizerQuotient,
    MonoidHom.ker_comp_of_injective _ _ (hK.symm.QuotientMulEquiv.trans eK).injective,
    QuotientGroup.ker_mk']

/-- The quotient kills exactly the original binary factor in the marked C(z). -/
public theorem normalizerQuotient_centralizer_eq_one_iff (x : TwistedModel) :
    normalizerQuotient D k K hK eK (normalizerCentralizer D k x) = 1 ↔ x.right = 1 := by
  change normalizerCentralizer D k x ∈ (normalizerQuotient D k K hK eK).ker ↔ _
  rw [normalizerQuotient_ker, normalizerCentralizer_mem_E]

/-- The marked S4 actors remain distinct after passing to the A6 quotient. -/
public theorem normalizerQuotient_actor_injective :
    Function.Injective ((normalizerQuotient D k K hK eK).comp (normalizerActor D k)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro s hs
  rw [Subgroup.mem_bot]
  exact (normalizerQuotient_centralizer_eq_one_iff D k K hK eK
    (SemidirectProduct.inr s)).mp hs

/-- Local analysis constructs a surjection onto the actual A6 carrier with
exactly the prescribed E kernel. -/
public theorem exists_normalizerQuotient (L : LocalAnalysisData D k) :
    ∃ π : normalizer (CaseII.E D k : Set G) →* alternatingGroup (Fin 6),
      Function.Surjective π ∧
      π.ker = (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := L.normalizer_E
  exact ⟨normalizerQuotient D k K hK eK,
    normalizerQuotient_surjective D k K hK eK, normalizerQuotient_ker D k K hK eK⟩

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
