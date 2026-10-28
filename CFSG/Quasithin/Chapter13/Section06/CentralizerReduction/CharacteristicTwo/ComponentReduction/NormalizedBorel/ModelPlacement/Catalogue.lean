module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Catalogue.Control
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionBorels.Alignment

/-!
# Complete-catalogue Borel markings and their placement application

Every large-field `BinaryModelAt` witness admits a concrete standard carrier
and an actual equivalence taking any supplied Sylow to its positive root
subgroup. Its normalizer is the published matrix/root Borel. This marking
result includes triality and Ree–F₄ without extra premises.

Solvable control is proved for all eight families, including unrestricted
genuine triality. It places the actual residual in the relative Borel
candidate. In inner cases the same marked component equivalence extends
to K*Lᵥ* = K*, so the literal candidate and residual images lie in the
concrete Borel. Exceptional covers are handled on the actual component
image. The unconditional applications below discharge the catalogue
premise of this step in 13.6.6; its other source branches remain separate.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, with A.2.3–4
and 1.1.5(3a,b).
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
open Subgroup Theory.GroupTheory A5Module

/-- A complete concrete marking of the supplied Sylow and its normalizer.
The Borel and positive roots are the independently defined matrix/root
subgroups of `StandardModel`, not arbitrary subgroups chosen afterwards. -/
theorem exists_aligned_model {D : Type*} [Group D] [Finite D] {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt D m) (hm : 1 < m) (S : Sylow 2 D) :
    ∃ (M : StandardModel m) (e : D ≃* M.Carrier),
      (S : Subgroup D).map e.toMonoidHom = M.U ∧
      (normalizer (S : Set D)).map e.toMonoidHom = M.B := by
  obtain ⟨M, ⟨e⟩⟩ := exists_standardModel hmodel hm
  obtain ⟨Q, hQ⟩ := M.exists_sylow
  obtain ⟨g, e', _, hS⟩ := SolvableSylowControl.exists_aligned_equiv e S Q
  refine ⟨M, e', hS.trans hQ, ?_⟩
  change (normalizer ((S : Subgroup D) : Set D)).map e'.toMonoidHom = M.B
  rw [map_equiv_normalizer_eq, hS, hQ]
  exact M.normalizer_U

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The original conditional consumer of the intrinsic catalogue theorem.
The marking supplies solvability, normalization and the literal Sylow image.
See `residualStar_le_borelCandidate_of_binaryModel` for the discharged form. -/
theorem residualStar_le_borelCandidate_of_catalogue (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hm : 1 < m) (htriality : TrialityControl)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ borelCandidate s T K := by
  obtain ⟨M, ⟨e⟩⟩ := exists_standardModel hmodel hm
  exact residualStar_le_borelCandidate_of_model s T K e
    (M.control_of_triality htriality) hk hTL S hS hDN hTN

/-- In an inner case, construct compatible component and whole-overgroup
markings and apply `borelCandidate_model_map` through the checked alignment
consumer. Its output retains the literal quotient and embedded Sylow. -/
theorem exists_inner_borel_data_of_catalogue (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hm : 1 < m) (htriality : TrialityControl)
    (hinner : residualStar s K ≤ NormalizerAction.componentImage K)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    ∃ M : StandardModel m,
      Nonempty (ExtensionBorels.CompatibleBorelData s T K
        (MonoidHom.id M.Carrier) M.U M.B) := by
  obtain ⟨M, ⟨k⟩⟩ := exists_standardModel hmodel hm
  obtain ⟨Q, hQ⟩ := M.exists_sylow
  let e := (MulEquiv.subgroupCongr (sup_eq_left.mpr hinner)).trans k
  have hc (x : NormalizerAction.componentImage K) :
      e ⟨x.val, mem_sup_left x.property⟩ = (MonoidHom.id M.Carrier) (k x) := rfl
  have hB : normalizer ((Q : Subgroup M.Carrier).map (MonoidHom.id M.Carrier) :
      Set M.Carrier) = M.B := by
    rw [Subgroup.map_id, hQ]
    exact M.normalizer_U
  obtain ⟨g, d, _, _⟩ := ExtensionBorels.exists_compatibleBorelData s T K
    (MonoidHom.id M.Carrier) e k hc Q M.B hB hk hTL S hS hDN hTN
    ((M.control_of_triality htriality).of_equiv k)
  exact ⟨M, ⟨hQ ▸ d⟩⟩

/-- The complete intrinsic catalogue discharges the model-control premise
of the actual residual-placement consumer, including non-inner cases.
The model is that of K* = K/Z(K), so exceptional covers are retained. -/
theorem residualStar_le_borelCandidate_of_binaryModel (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hm : 1 < m)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ borelCandidate s T K := by
  obtain ⟨M, ⟨e⟩⟩ := exists_standardModel hmodel hm
  exact residualStar_le_borelCandidate_of_model s T K e M.solvableSylowControl
    hk hTL S hS hDN hTN

/-- In inner cases the complete catalogue constructs compatible concrete
Borel markings, with the actual candidate and residual images, and no
additional intrinsic-control premise. -/
theorem exists_inner_borel_data_of_binaryModel (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ}
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hm : 1 < m) (hinner : residualStar s K ≤ NormalizerAction.componentImage K)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    ∃ M : StandardModel m,
      Nonempty (ExtensionBorels.CompatibleBorelData s T K
        (MonoidHom.id M.Carrier) M.U M.B) :=
  exists_inner_borel_data_of_catalogue s T K hmodel hm trialityControl hinner
    hk hTL S hS hDN hTN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.Catalogue
