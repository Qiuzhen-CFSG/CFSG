module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Catalogue
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.SmallRankOuter
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Assembly of normalized-component Borel placement

The full binary catalogue supplies solvable Sylow control. Case (i) maps
residual containment through the literal normalizer quotient; case (ii)
uses the proved small-three-rank outer calculation and perfect central
cover descent. Both therefore use a concrete component Borel. Case (iii)
uses the actual diagonal or mixed outer-preimage presentation, preserving
the component embedding while aligning the supplied Sylow.

`Alternatives` is the earlier source classification input, with all three
branches and the ambient prime-to residual equality retained. It asserts
no Borel placement, root normalization or symplectic identification.
The incompatible legacy `A316Nonsplit` interface is deliberately not used.
Its producer must instead supply `ExtensionPresentation` on the actual
whole overgroup; constructing that earlier source classification is outside
this conditional Borel argument.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927, from “Hence
Tᵥ = T_X” through Lᵥ* ≤ B*, with A.3.16–18 and A.2.3–4.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ModelPlacement
open Subgroup Theory.GroupTheory A5Module

variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- An actual extension equivalence with the component embedding retained.
It contains no root marking or normalizer conclusion. -/
structure ExtensionPresentation (s : Marking L V)
    (K : Subgroup (Gv (markedV s))) {m : ℕ} (M : ExtensionModel m) where
  overgroupEquiv : (NormalizerAction.componentImage K ⊔ residualStar s K :
    Subgroup (XStar K)) ≃* M.Carrier
  componentEquiv : NormalizerAction.componentImage K ≃* M.Component
  compatible : ∀ x : NormalizerAction.componentImage K,
    overgroupEquiv ⟨x.val, mem_sup_left x.property⟩ = M.embedding (componentEquiv x)

/-- All three source branches, with the correct residual conventions.
In the third branch K = O^{3'}(E(Gᵥ)) as an ambient subgroup, and the
whole K*Lᵥ* has one of the four concrete compatible presentations. -/
inductive Alternatives (s : Marking L V) (K : Subgroup (Gv (markedV s))) (m : ℕ) : Prop
  | residual (hres : residual s ≤ primeToResidual 3 (Gv (markedV s)))
      (hK : K = primeToResidual 3 (Gv (markedV s))) : Alternatives s K m
  | rankOne (hr : primeRank 3 K ≤ 1) : Alternatives s K m
  | extension (M : ExtensionModel m) (hM : Nonempty (ExtensionPresentation s K M))
      (hK : K = (primeToResidual 3 (componentLayer (Gv (markedV s)))).map
        (componentLayer (Gv (markedV s))).subtype) : Alternatives s K m

/-- The complete output catalogue retains the model, its component and
whole-overgroup carriers, and its explicitly defined Borel. -/
inductive BorelModel (m : ℕ) : Type 1
  | inner (M : Catalogue.StandardModel m)
  | extension (M : ExtensionModel m)

namespace BorelModel

def Component {m : ℕ} (M : BorelModel m) : Type := by
  cases M with
  | inner M => exact M.Carrier
  | extension M => exact M.Component

instance {m : ℕ} (M : BorelModel m) : Group M.Component := by
  cases M <;> simp only [Component] <;> infer_instance

def Carrier {m : ℕ} (M : BorelModel m) : Type := by
  cases M with
  | inner M => exact M.Carrier
  | extension M => exact M.Carrier

instance {m : ℕ} (M : BorelModel m) : Group M.Carrier := by
  cases M <;> simp only [Carrier] <;> infer_instance

def embedding {m : ℕ} (M : BorelModel m) : M.Component →* M.Carrier := by
  cases M with
  | inner M => exact MonoidHom.id M.Carrier
  | extension M => exact M.embedding

def U {m : ℕ} (M : BorelModel m) : Subgroup M.Component := by
  cases M with
  | inner M => exact M.U
  | extension M => exact (M.sylow : Subgroup M.Component)

def B {m : ℕ} (M : BorelModel m) : Subgroup M.Carrier := by
  cases M with
  | inner M => exact M.B
  | extension M => exact M.B

end BorelModel

/-- The literal inner containment in both source cases (i) and (ii), with
all model outer-abelianness and central-cover premises discharged. -/
theorem residualStar_le_component_of_inner_cases
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hcases : (residual s ≤ primeToResidual 3 (Gv (markedV s)) ∧
      K = primeToResidual 3 (Gv (markedV s))) ∨ primeRank 3 K ≤ 1)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    residualStar s K ≤ NormalizerAction.componentImage K := by
  rcases hcases with ⟨hres, heq⟩ | hr
  · exact residualStar_le_of_le s K (hres.trans_eq heq.symm)
  · exact residualStar_le_of_binaryModelAt_small_three_rank s T K hK hm hmodel hr
      hk hTL S hS hDN hTN

/-- The complete source alternative constructs a concrete compatible Borel
marking of the actual K*Lᵥ*. Solvable control, root normalization and Sylow
alignment are proved here, rather than additional input certificates. -/
theorem exists_borel_data
    (s : Marking L V) (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (halt : Alternatives s K m)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K) :
    ∃ M : BorelModel m,
      Nonempty (ExtensionBorels.CompatibleBorelData s T K M.embedding M.U M.B) := by
  have inner_case (hinner : residualStar s K ≤ NormalizerAction.componentImage K) :
      ∃ M : BorelModel m,
        Nonempty (ExtensionBorels.CompatibleBorelData s T K M.embedding M.U M.B) := by
    obtain ⟨M, hd⟩ := Catalogue.exists_inner_borel_data_of_binaryModel s T K hmodel hm
      hinner hk hTL S hS hDN hTN
    exact ⟨.inner M, hd⟩
  cases halt with
  | residual hres heq => exact inner_case (residualStar_le_of_le s K (hres.trans_eq heq.symm))
  | rankOne hr =>
    exact inner_case (residualStar_le_of_binaryModelAt_small_three_rank s T K hK hm
      hmodel hr hk hTL S hS hDN hTN)
  | extension M hd _ =>
    obtain ⟨d⟩ := hd
    obtain ⟨g, b, _, _⟩ := ExtensionBorels.exists_compatibleBorelData s T K M.embedding
      d.overgroupEquiv d.componentEquiv d.compatible M.sylow M.B M.normalizer_root
      hk hTL S hS hDN hTN (Catalogue.control hmodel hm)
    exact ⟨.extension M, ⟨b⟩⟩

/-- Actual source application: retain the marked action asymmetry, the
central four-group in R*, and the constructed compatible Borel together.
The independent root-rigidity branch can use this data to identify Sp₄. -/
theorem source_borel_and_action
    {κ : GroupClass} {T : Sylow 2 G} {s : Marking L V}
    (d : InitialSieve.Setup κ T s)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : InitialSieve.ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 1 < m)
    (hmodel : InitialSieve.BinaryModelAt (NormalizerAction.componentImage K) m)
    (hEK : EStar s K a.a_normalizes a.z_normalizes ≤ NormalizerAction.componentImage K)
    (halt : Alternatives s K m)
    (hk : IsPGroup 2 s.action.ker) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTN : localT (T : Subgroup G) (markedV s) ≤ X K) :
    residualStar s K ≤ borelCandidate s (T : Subgroup G) K ∧
      EStar s K a.a_normalizes a.z_normalizes ≤ rootCenter (T : Subgroup G) K ∧
      ⁅residualStar s K, zpowers (zStar s K a.z_normalizes)⁆ ≠ ⊥ ∧
      ⁅residualStar s K, zpowers (aStar s K a.a_normalizes)⁆ = ⊥ ∧
      ∃ M : BorelModel m,
        Nonempty (ExtensionBorels.CompatibleBorelData s (T : Subgroup G) K
          M.embedding M.U M.B) := by
  have hS : (d.sylow : Subgroup (Gv (markedV s))) = localT (T : Subgroup G) (markedV s) :=
    (InitialSieve.localT_eq_sylow _ _ d.sylow d.sylow_image).symm
  have hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))) := by
    intro x hx
    exact Subtype.ext (d.a_centralizes x hx)
  obtain ⟨hz, ha⟩ := marked_action_asymmetry s K hK a.a_normalizes a.z_normalizes
    a.residual_normalizes hac d.centralizer_cores.2
  exact ⟨Catalogue.residualStar_le_borelCandidate_of_binaryModel s (T : Subgroup G) K
      hmodel hm hk hTL d.sylow hS a.residual_normalizes hTN,
    four_le_rootCenter s (T : Subgroup G) K a.a_normalizes a.z_normalizes a.central hEK,
    hz, ha, exists_borel_data s (T : Subgroup G) K hK hm hmodel halt hk hTL
      d.sylow hS a.residual_normalizes hTN⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel.ModelPlacement
