module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Compatible
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Overgroups
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.ExtensionModels

/-!
# All four signed-three extension branches

The compatible placement output supplies the actual component marking of
the specified Sylow intersection. Central descent through that marking
lets the source residual identity remove field action before the root
calculation. Uniformity then holds throughout the actual relative Borel,
for each nonidentity element of R*, including both a* and z*.

The four constructors retain PGL₃ with even degree, PGU₃ with odd degree,
the linear mixed outer preimage with degree divisible by six, and the
unitary mixed preimage with odd degree divisible by three. Their whole
overgroup equivalences and compatible component embeddings are retained;
no nonsplit extension is replaced by a split one. The earlier source
classification supplies those equivalences through the placement owner.

Source: Aschbacher–Smith, A.3.16–18 and proof of 13.6.6, printed p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- Central descent from a component marking is precisely its inverse
embedding in the literal quotient. This holds for central covers as well. -/
@[simp] theorem rankOneModelEmbedding_of_componentEquiv {M : Type*} [Group M] {v : G}
    (K : Subgroup (Gv v)) (e : NormalizerAction.componentImage K ≃* M) :
    rankOneModelEmbedding K ((NormalizerAction.componentCentralQuotientEquiv K).trans e) =
      (NormalizerAction.componentImage K).subtype.comp e.symm.toMonoidHom := by
  ext x
  change ((NormalizerAction.componentCentralQuotientEquiv K)
    ((NormalizerAction.componentCentralQuotientEquiv K).symm (e.symm x)) : XStar K) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

variable [Finite G]

namespace ModelPlacement.ExtensionModel

/-- The highest linear root or the fixed-field unitary central root,
inside the genuinely embedded component of the extension. -/
@[expose] def rootElements {m : ℕ} (M : ExtensionModel m) : Set M.Component := by
  cases M with
  | linearDiagonal F _ _ _ =>
    exact (Matrix.PSL3.OuterSolvable.OddPrimeCoverage.rootGroup
      (F := F) (by decide : (0 : Fin 3) ≠ 2)).carrier
  | linearMixed F _ _ _ =>
    exact (Matrix.PSL3.OuterSolvable.OddPrimeCoverage.rootGroup
      (F := F) (by decide : (0 : Fin 3) ≠ 2)).carrier
  | unitaryDiagonal F J hJ hm hF hconj hmod =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact (HermitianForm.BorelTorus.EvenCenterAction.centralImage J hJ).carrier
  | unitaryMixed F J hJ hm hF hconj hthree hmod σ hfield a hdiag houter =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact (HermitianForm.BorelTorus.EvenCenterAction.centralImage J hJ).carrier

/-- The full center of the actual component Sylow in every signed-three
extension, with the quadratic and fixed fields kept distinct. -/
theorem center_eq_rootElements {m : ℕ} (M : ExtensionModel m) :
    (((center (M.sylow : Subgroup M.Component)).map (M.sylow : Subgroup M.Component).subtype :
      Subgroup M.Component) : Set M.Component) = M.rootElements := by
  cases M with
  | linearDiagonal F hm hF hmod =>
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (Matrix.PSL3.NormalizedRootCentralizers.center_unipotent_eq_rootGroup (F := F))
  | linearMixed F hm hF D =>
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (Matrix.PSL3.NormalizedRootCentralizers.center_unipotent_eq_rootGroup (F := F))
  | unitaryDiagonal F J hJ hm hF hconj hmod =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (HermitianForm.NormalizedRootCentralizers.root_center J hm hF
        (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj) hJ)
  | unitaryMixed F J hJ hm hF hconj hthree hmod σ hfield a hdiag houter =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (HermitianForm.NormalizedRootCentralizers.root_center J hm hF
        (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj) hJ)

end ModelPlacement.ExtensionModel

omit [Finite G] in
/-- The root identification retains the extension's compatible component
embedding, including the literal mixed outer preimages. -/
theorem extension_rootCenter_eq (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ} (M : ModelPlacement.ExtensionModel m)
    (d : ExtensionBorels.CompatibleBorelData s T K M.embedding M.sylow M.B) :
    (rootCenter T K : Set (XStar K)) =
      ((NormalizerAction.componentImage K).subtype.comp d.componentEquiv.symm.toMonoidHom) ''
        M.rootElements := by
  rw [rootCenter_eq_model_center T K _
    (Subtype.val_injective.comp d.componentEquiv.symm.injective) (M.sylow : Subgroup M.Component) d.component_sylow_image,
    coe_map, M.center_eq_rootElements]

/-- Complete uniformity in the actual source relative Borel in all four
extension models, with the component/Sylow alignment supplied by placement. -/
theorem extension_root_centralizers (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    {m : ℕ} (M : ModelPlacement.ExtensionModel m)
    (d : ExtensionBorels.CompatibleBorelData s T K M.embedding M.sylow M.B)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hcomm : ⁅residual s, localT T (markedV s)⁆ = residual s)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    borelCandidate s T K ⊓ centralizer ({r} : Set (XStar K)) =
      borelCandidate s T K ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
  cases M with
  | linearDiagonal F hm hF hmod =>
    apply linearThree_borel_root_centralizers s T K hm hF
      ((NormalizerAction.componentCentralQuotientEquiv K).trans d.componentEquiv) _
      hDN hTN hcomm r hr hne
    erw [linearThreeEmbedding_of_componentEquiv]
    exact d.component_sylow_image
  | linearMixed F hm hF D =>
    apply linearThree_borel_root_centralizers s T K hm hF
      ((NormalizerAction.componentCentralQuotientEquiv K).trans d.componentEquiv) _
      hDN hTN hcomm r hr hne
    erw [linearThreeEmbedding_of_componentEquiv]
    exact d.component_sylow_image
  | unitaryDiagonal F J hJ hm hF hconj hmod =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    apply unitaryThree_borel_root_centralizers s T K hK J hJ hm hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj)
      ((NormalizerAction.componentCentralQuotientEquiv K).trans d.componentEquiv) _
      hDN hTN hcomm r hr hne
    erw [rankOneModelEmbedding_of_componentEquiv]
    exact d.component_sylow_image
  | unitaryMixed F J hJ hm hF hconj hthree hmod σ hfield a hdiag houter =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    apply unitaryThree_borel_root_centralizers s T K hK J hJ hm hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj)
      ((NormalizerAction.componentCentralQuotientEquiv K).trans d.componentEquiv) _
      hDN hTN hcomm r hr hne
    erw [rankOneModelEmbedding_of_componentEquiv]
    exact d.component_sylow_image

/-- Actual application to the marked action asymmetry. The source commutator
identity is proved from the module marking and local Sylow, not an input. -/
theorem exclude_extensions (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K)
    (hDN : residual s ≤ X K) (hTN : localT T (markedV s) ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (hk : IsPGroup 2 s.action.ker) (hTL : T ≤ normalizer (L : Set G))
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))) = localT T (markedV s))
    {m : ℕ} (M : ModelPlacement.ExtensionModel m)
    (d : ExtensionBorels.CompatibleBorelData s T K M.embedding M.sylow M.B) : False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER
    (borelCandidate s T K) d.placement
    (extension_root_centralizers s T K hK M d hDN hTN (residual_commutator s T hk hTL S hS))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
