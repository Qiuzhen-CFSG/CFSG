module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity

/-!
# The normalized component has symplectic image

Start with the genuine marked local configuration, a component normalized
by Tᵥ, the complete large-field binary catalogue and all three alternatives
on printed p.927. The extension branch is eliminated using its compatible
whole-group presentation, constructed Borel and the uniform root
centralizer calculation. In the remaining two branches, the residual image
lies in K*. Aligning the prescribed component Sylow with the model Sylow
constructs a compatible Borel. The root calculations exclude each of the
seven nonsymplectic models, leaving an actual Sp₄(F) equivalence with
|F| = 2ᵐ and the same specified Sylow and Borel.

The original (i)/(ii) provenance is retained: an inner action alone does
not imply that the residual itself lies in K. The exceptional covers are
handled through K* = K/Z(K), without asserting that K is centerless. The
later whole-component and torus argument belongs to `SymplecticInputs`.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, from “Hence
Tᵥ = T_X” through K* ≅ Sp₄(2ᵐ), with 1.1.5(3a,b) and A.3.16–18.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open Theory.SpecificGroups.SymplecticFour

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Output of the reduction, retaining the actual finite field and the
compatible component, whole-overgroup, Sylow and Borel markings. -/
structure SymplecticBorelData (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (m : ℕ) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  cardinality : Nat.card F = 2 ^ m
  marking : ExtensionBorels.CompatibleBorelData s T K
    (MonoidHom.id (Sp F)) unipotent borel

attribute [instance] SymplecticBorelData.field SymplecticBorelData.finite SymplecticBorelData.charTwo

variable {κ : GroupClass} {T : Sylow 2 G} {s : Marking L V}

/-- Exclude all four signed-three presentations in alternative (iii), using
constructed Borel placement and the root calculation at the actual a*.
The original residual and small-three-rank alternatives are preserved. -/
theorem source_inner_alternatives
    (d : InitialSieve.Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : InitialSieve.ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (halt : ModelPlacement.Alternatives s K m)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K) :
    (residual s ≤ primeToResidual 3 (Gv (markedV s)) ∧
      K = primeToResidual 3 (Gv (markedV s))) ∨ primeRank 3 K ≤ 1 := by
  cases halt with
  | residual hres heq => exact Or.inl ⟨hres, heq⟩
  | rankOne hr => exact Or.inr hr
  | extension M hd _ =>
    obtain ⟨e⟩ := hd
    have hS : (d.sylow : Subgroup (Gv (markedV s))) = localT (T : Subgroup G) (markedV s) :=
      (InitialSieve.localT_eq_sylow _ _ d.sylow d.sylow_image).symm
    obtain ⟨g, b, _, _⟩ := ExtensionBorels.exists_compatibleBorelData s (T : Subgroup G) K
      M.embedding e.overgroupEquiv e.componentEquiv e.compatible M.sylow M.B
      M.normalizer_root hk hTL d.sylow hS a.residual_normalizes hTN (Catalogue.control hmodel hm)
    have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
      intro x hx
      exact Subtype.ext (d.a_centralizes x hx)
    exact False.elim (exclude_extensions s (T : Subgroup G) K hK
      a.a_normalizes a.z_normalizes a.residual_normalizes hTN hac
      (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.1)
      (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.2)
      (four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK)
      hk hTL d.sylow hS M b)

/-- The complete catalogue reduces to an actual symplectic model, with
Borel and Sylow markings constructed from the source arrangement. -/
theorem source_symplectic_borel
    (d : InitialSieve.Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : InitialSieve.ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (halt : ModelPlacement.Alternatives s K m)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K) :
    ((residual s ≤ primeToResidual 3 (Gv (markedV s)) ∧
      K = primeToResidual 3 (Gv (markedV s))) ∨ primeRank 3 K ≤ 1) ∧
    Nonempty (SymplecticBorelData s (T : Subgroup G) K m) := by
  have hcases := source_inner_alternatives d K hK a hm hmodel hEK halt hk hTL hTN
  refine ⟨hcases, ?_⟩
  have hS : (d.sylow : Subgroup (Gv (markedV s))) = localT (T : Subgroup G) (markedV s) :=
    (InitialSieve.localT_eq_sylow _ _ d.sylow d.sylow_image).symm
  have hinner := ModelPlacement.residualStar_le_component_of_inner_cases
    s (T : Subgroup G) K hK hm hmodel hcases hk hTL d.sylow hS a.residual_normalizes hTN
  obtain ⟨M, ⟨b⟩⟩ := Catalogue.exists_inner_borel_data_of_binaryModel
    s (T : Subgroup G) K hmodel hm hinner hk hTL d.sylow hS a.residual_normalizes hTN
  have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (d.a_centralizes x hx)
  have hexclude (hM : M.Nonsymplectic) : False :=
    exclude_nonsymplectic_catalogue s (T : Subgroup G) K
      a.a_normalizes a.z_normalizes a.residual_normalizes hac
      (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.1)
      (hK.not_centralizes_of_twoCore_centralizer _ d.centralizer_cores.2)
      (four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK)
      M hM b
  cases M with
  | symplecticFour F hm hF => exact ⟨{ F := F, cardinality := hF, marking := b }⟩
  | _ => exact (hexclude trivial).elim

/-- The complete normalized-component conclusion on p.927, with the original
source alternatives retained for the subsequent whole-component argument.
The Borel is the actual relative normalizer and the returned model marking
identifies both it and the specified component Sylow. -/
theorem source_symplectic_reduction
    (d : InitialSieve.Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : InitialSieve.ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (halt : ModelPlacement.Alternatives s K m)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K) :
    localT (T : Subgroup G) (markedV s) ⊓ X K = localT (T : Subgroup G) (markedV s) ∧
      ⁅residual s, localT (T : Subgroup G) (markedV s)⁆ = residual s ∧
      residualStar s K ≤ NormalizerAction.componentImage K ∧
      residualStar s K ≤ borelCandidate s (T : Subgroup G) K ∧
      EStar s K a.a_normalizes a.z_normalizes ≤ rootCenter (T : Subgroup G) K ∧
      ⁅residualStar s K, zpowers (zStar s K a.z_normalizes)⁆ ≠ ⊥ ∧
      ⁅residualStar s K, zpowers (aStar s K a.a_normalizes)⁆ = ⊥ ∧
      ((residual s ≤ primeToResidual 3 (Gv (markedV s)) ∧
        K = primeToResidual 3 (Gv (markedV s))) ∨ primeRank 3 K ≤ 1) ∧
      Nonempty (SymplecticBorelData s (T : Subgroup G) K m) := by
  obtain ⟨hcases, ⟨b⟩⟩ := source_symplectic_borel d K hK a hm hmodel hEK halt hk hTL hTN
  have hS : (d.sylow : Subgroup (Gv (markedV s))) = localT (T : Subgroup G) (markedV s) :=
    (InitialSieve.localT_eq_sylow _ _ d.sylow d.sylow_image).symm
  have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (d.a_centralizes x hx)
  obtain ⟨hz, ha⟩ := marked_action_asymmetry s K hK a.a_normalizes a.z_normalizes
    a.residual_normalizes hac d.centralizer_cores.2
  exact ⟨inf_eq_left.mpr hTN, residual_commutator s (T : Subgroup G) hk hTL d.sylow hS,
    ModelPlacement.residualStar_le_component_of_inner_cases s (T : Subgroup G) K hK hm
      hmodel hcases hk hTL d.sylow hS a.residual_normalizes hTN,
    b.marking.placement,
    four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK,
    hz, ha, hcases, ⟨b⟩⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
