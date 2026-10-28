module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement
public import Theory.GroupTheory.EmbeddedSylowAlignment
public import Theory.GroupTheory.AutomorphismExtensionBorel

/-!
# Compatible markings of the extension Borel

Starting with an equivalence on the whole K*Lᵥ* and its compatibility with
the embedded component, choose a component conjugation that aligns the
literal Tᵥ* ∩ K* with the model root Sylow. The same conjugation adjusts
both equivalences. The published intrinsic placement theorem then supplies
the Borel image and the residual containment in that marking.

For outer-quotient preimages the embedded root normalizer is obtained from
the concrete actor stabilizer calculation. That matrix calculation and the
earlier source extension alternative remain inputs here; no splitting of
the preimage is used or asserted.

Source: Aschbacher–Smith, Notation A.3.16 and Lemma A.3.18, printed pp.51–52,
and the Borel placement in the proof of 13.6.6, printed p.927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ExtensionBorels
open Subgroup Theory.GroupTheory A5Module
open AutomorphismExtensionBorel

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Borel data in a single marking of the whole overgroup. These are the
conclusions of the alignment construction, not source hypotheses. -/
structure CompatibleBorelData (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M H : Type*} [Group M] [Group H]
    (i : M →* H) (U : Subgroup M) (B : Subgroup H) where
  overgroupEquiv : (NormalizerAction.componentImage K ⊔ residualStar s K :
    Subgroup (XStar K)) ≃* H
  componentEquiv : NormalizerAction.componentImage K ≃* M
  compatible : ∀ x : NormalizerAction.componentImage K,
    overgroupEquiv ⟨x.val, Subgroup.mem_sup_left x.property⟩ = i (componentEquiv x)
  sylow_image : ((NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
    NormalizerAction.componentImage K).subgroupOf
      (NormalizerAction.componentImage K ⊔ residualStar s K)).map
        overgroupEquiv.toMonoidHom = U.map i
  root_normalizer : normalizer (U.map i : Set H) = B
  placement : residualStar s K ≤ borelCandidate s T K
  candidate_image : ((borelCandidate s T K).subgroupOf
    (NormalizerAction.componentImage K ⊔ residualStar s K)).map
      overgroupEquiv.toMonoidHom = B
  residual_image : ((residualStar s K).subgroupOf
    (NormalizerAction.componentImage K ⊔ residualStar s K)).map
      overgroupEquiv.toMonoidHom ≤ B

/-- The alignment is constructed for the supplied Sylow, by conjugating the
whole equivalence by an element of the embedded model component. The source
component-control premise is retained for the catalogue owner. -/
theorem exists_compatibleBorelData (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M H : Type*} [Group M] [Group H]
    (i : M →* H)
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃* H)
    (k : NormalizerAction.componentImage K ≃* M)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ = i (k x))
    (Q : Sylow 2 M) (B : Subgroup H)
    (hB : normalizer ((Q : Subgroup M).map i : Set H) = B)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : M) (d : CompatibleBorelData s T K i Q B),
      d.overgroupEquiv = e.trans (MulAut.conj (i m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  let : Finite M := Finite.of_equiv _ k.toEquiv
  obtain ⟨P, hP⟩ := NormalizerAction.exists_component_sylow K S (hS ▸ hTN)
  rw [hS] at hP
  obtain ⟨m, e', k', he', hk', hc, _, hU⟩ :=
    EmbeddedSylowAlignment.exists_compatible_marking
      (NormalizerAction.componentImage K) _ le_sup_left i e k hcompat P Q
  rw [hP] at hU
  obtain ⟨hplace, hcandidate, hresidual⟩ :=
    residualStar_model_borel_data s T K e' _ B hU hB hk hTL S hS hDN hTN hcontrol
  exact ⟨m, ⟨e', k', hc, hU, hB, hplace, hcandidate, hresidual⟩, he', hk'⟩

/-- Apply the alignment to a literal outer-quotient preimage. The remaining
intrinsic model input is the concrete root/torus/semilinear actor calculation;
it supplies the normalizer equation used by `ModelPlacement`. -/
theorem exists_outerPreimage_borel_data (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {M : Type*} [Group M]
    (D : Subgroup (MulAut.Outer M))
    (e : (NormalizerAction.componentImage K ⊔ residualStar s K :
      Subgroup (XStar K)) ≃* outerPreimage D)
    (k : NormalizerAction.componentImage K ≃* M)
    (hcompat : ∀ x : NormalizerAction.componentImage K,
      e ⟨x.val, Subgroup.mem_sup_left x.property⟩ =
        innerEmbedding (outerPreimage D) (inner_le_outerPreimage D) (k x))
    (Q : Sylow 2 M) (B : Subgroup (MulAut M))
    (hi : Function.Injective (MulAut.conj : M →* MulAut M))
    (hB : ∀ a : outerPreimage D,
      (Q : Subgroup M).map a.val.toMonoidHom = Q ↔ a.val ∈ B)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcontrol : SolvableSylowControl 2 (NormalizerAction.componentImage K)) :
    ∃ (m : M) (d : CompatibleBorelData s T K
      (innerEmbedding (outerPreimage D) (inner_le_outerPreimage D)) Q
      (B.subgroupOf (outerPreimage D))),
      d.overgroupEquiv = e.trans (MulAut.conj
        (innerEmbedding (outerPreimage D) (inner_le_outerPreimage D) m)) ∧
      d.componentEquiv = k.trans (MulAut.conj m) := by
  have hn := normalizer_rootIn (Q : Subgroup M) (outerPreimage D) B
    (inner_le_outerPreimage D) hi hB
  rw [rootIn_eq_map _ _ (inner_le_outerPreimage D)] at hn
  exact exists_compatibleBorelData s T K _ e k hcompat Q _ hn
    hk hTL S hS hDN hTN hcontrol

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ExtensionBorels
