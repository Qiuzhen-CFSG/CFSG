module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Compatible
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.RankOne
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.LinearThree
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.G2
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.Triality
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.RootRigidity.ReeF4
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.NormalizedBorel.ModelPlacement.Catalogue.Carriers
public import Theory.SpecificGroups.Suzuki.NormalizedRootCentralizers

/-!
# The complete nonsymplectic inner Borel catalogue

Every nonsymplectic constructor of the actual large-field catalogue has
uniform Borel centralizers on its full positive Sylow center. The proof
uses the coordinate calculations for PSL₂, PSU₃, Suzuki, PSL₃, G₂, genuine
triality and Ree F₄. The unitary matrix field has order q² and its fixed
field has order q. The compatible placement output transports these
calculations to the literal R* = Z(Tᵥ* ∩ K*) and B* in N(K)/C(K).

The symplectic constructor is deliberately separate. The parent's final
identification can eliminate all seven other constructors with the theorem
below; no model equivalence, placement, or root calculation is hidden in a tag.

Source: Aschbacher–Smith A.2.3–4, 1.1.5(3a,b), proof of 13.6.6, p.927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BenderSuzuki.MatrixGroups

namespace Catalogue.StandardModel

/-- Select the seven concrete nonsymplectic presentations in the catalogue. -/
def Nonsymplectic {m : ℕ} (M : Catalogue.StandardModel m) : Prop := by
  cases M with
  | symplecticFour F hm hF => exact False
  | _ => exact True

/-- The actual coordinate root in each nonsymplectic model. The symplectic
slot is unused: its Sylow center is not asserted to be one root subgroup. -/
def rootElements {m : ℕ} (M : Catalogue.StandardModel m) : Set M.Carrier := by
  cases M with
  | linearTwo F _ _ => exact (BenderSuzuki.Converse.PUnip F).carrier
  | unitaryThree F J hJ hm hF hconj =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact (HermitianForm.BorelTorus.EvenCenterAction.centralImage J hJ).carrier
  | suzuki n _ =>
    exact {r : SuzukiMatrixGroup n | ∃ b : BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * n + 1),
      (r : Matrix.GeneralLinearGroup (Fin 4) (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * n + 1))) =
        SuzukiRootGL n 0 b}
  | linearThree F _ _ =>
    exact (Matrix.PSL3.OuterSolvable.OddPrimeCoverage.rootGroup
      (F := F) (by decide : (0 : Fin 3) ≠ 2)).carrier
  | symplecticFour F _ _ => exact ∅
  | g2 F _ _ => exact (Atlas.G2.LieParabolicSetup.highestRoot (F := F)).carrier
  | triality n hn =>
    exact (Triality.Standard.RadicalCoordinates.Centers.highestRoot
      (Triality.Standard.binaryParameters m (by omega)) :
        Set (Triality.Standard.Carrier (Triality.Standard.binaryParameters m (by omega))))
  | ree n _ => exact (ReeF4.EvenInvolutionGeometry.longRootGroup n).carrier

/-- The whole model Sylow center, with both inclusions, is the specified
coordinate root. No root identification is an input to the calculation. -/
theorem center_eq_rootElements {m : ℕ} (M : Catalogue.StandardModel m)
    (hM : M.Nonsymplectic) :
    (((center M.U).map M.U.subtype : Subgroup M.Carrier) : Set M.Carrier) = M.rootElements := by
  cases M with
  | linearTwo F hm hF =>
    have he : BenderSuzuki.Converse.PUnip F =
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F := by
      rw [BenderSuzuki.Converse.PUnip, BenderSuzuki.Converse.Unip, ← MonoidHom.range_comp]
      rfl
    have h := Matrix.ProjectiveSpecialLinearGroup.NormalizedRootCentralizers.center_kernel F
    rw [← he] at h
    exact congrArg (fun A : Subgroup _ => A.carrier) h
  | unitaryThree F J hJ hm hF hconj =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (HermitianForm.NormalizedRootCentralizers.root_center J hm hF
        (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj) hJ)
  | suzuki n hn =>
    ext r
    exact BenderSuzuki.MatrixGroups.NormalizedRootCentralizers.mem_center_iff_coordinates n (by omega) r
  | linearThree F hm hF =>
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (Matrix.PSL3.NormalizedRootCentralizers.center_unipotent_eq_rootGroup (F := F))
  | symplecticFour F hm hF => exact hM.elim
  | g2 F hm hF =>
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (Atlas.G2.LieParabolicSetup.unipotent_center (F := F))
  | triality n hn =>
    dsimp only [U, rootElements]
    erw [Triality.Standard.RadicalCoordinates.Centers.embedded_center_unipotent
      (Triality.Standard.binaryParameters m (by omega)) rfl]
    rfl
  | ree n hn =>
    exact congrArg (fun A : Subgroup _ => A.carrier)
      (ReeF4.EvenInvolutionGeometry.unipotent_center_eq_longRootGroup n (by omega))

/-- The complete seven-family calculation, using the full model Sylow center. -/
theorem root_centralizers {m : ℕ} (M : Catalogue.StandardModel m) (hM : M.Nonsymplectic)
    (r : M.Carrier) (hr : r ∈ (center M.U).map M.U.subtype) (hne : r ≠ 1) :
    M.B ⊓ centralizer ({r} : Set M.Carrier) =
      M.B ⊓ centralizer (((center M.U).map M.U.subtype : Subgroup M.Carrier) : Set M.Carrier) := by
  cases M with
  | linearTwo F hm hF =>
    have he : BenderSuzuki.Converse.PUnip F =
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.kernel F := by
      rw [BenderSuzuki.Converse.PUnip, BenderSuzuki.Converse.Unip, ← MonoidHom.range_comp]
      rfl
    have h := Matrix.ProjectiveSpecialLinearGroup.NormalizedRootCentralizers.uniform F
    rw [← he] at h
    exact h r hr hne
  | unitaryThree F J hJ hm hF hconj =>
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m * 2)
      (by simpa only [pow_mul, Nat.card_eq_fintype_card] using hF)
    exact HermitianForm.NormalizedRootCentralizers.uniform J hm hF
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 m (by omega) hF hconj) hJ r hr hne
  | suzuki n hn =>
    exact BenderSuzuki.MatrixGroups.NormalizedRootCentralizers.uniform
      n (by omega) _ r hr hne
  | linearThree F hm hF => exact Matrix.PSL3.NormalizedRootCentralizers.uniform _ r hr hne
  | symplecticFour F hm hF => exact hM.elim
  | g2 F hm hF => exact Atlas.G2.NormalizedRootCentralizers.uniform r hr hne
  | triality n hn => exact Triality.Standard.NormalizedRootCentralizers.uniform _ rfl r hr hne
  | ree n hn => exact ReeF4.NormalizedRootCentralizers.uniform n (by omega) r hr hne

end Catalogue.StandardModel

variable {G : Type*} [Group G] {L V : Subgroup G}

/-- Literal identification of R* with the model's actual coordinate root,
using the component map furnished by the placement producer. -/
theorem catalogue_rootCenter_eq (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ} (M : Catalogue.StandardModel m)
    (hM : M.Nonsymplectic)
    (d : ExtensionBorels.CompatibleBorelData s T K (MonoidHom.id M.Carrier) M.U M.B) :
    (rootCenter T K : Set (XStar K)) =
      ((NormalizerAction.componentImage K).subtype.comp d.componentEquiv.symm.toMonoidHom) ''
        M.rootElements := by
  rw [rootCenter_eq_model_center T K _
    (Subtype.val_injective.comp d.componentEquiv.symm.injective) M.U d.component_sylow_image,
    coe_map, M.center_eq_rootElements hM]

/-- The actual placement output supplies all maps and both subgroup alignments
needed for uniformity in the literal relative Borel. -/
theorem catalogue_root_centralizers (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) {m : ℕ} (M : Catalogue.StandardModel m)
    (hM : M.Nonsymplectic)
    (d : ExtensionBorels.CompatibleBorelData s T K (MonoidHom.id M.Carrier) M.U M.B)
    (r : XStar K) (hr : r ∈ rootCenter T K) (hne : r ≠ 1) :
    borelCandidate s T K ⊓ centralizer ({r} : Set (XStar K)) =
      borelCandidate s T K ⊓ centralizer (rootCenter T K : Set (XStar K)) :=
  root_centralizers_of_model T K _
    (Subtype.val_injective.comp d.componentEquiv.symm.injective) M.U M.B
    d.component_sylow_image (borelCandidate s T K) d.inner_borel_image.ge
    (M.root_centralizers hM) r hr hne

/-- The marked source configuration excludes every nonsymplectic inner
catalogue constructor, using the actual output of Borel placement. -/
theorem exclude_nonsymplectic_catalogue [Finite G] (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    {m : ℕ} (M : Catalogue.StandardModel m) (hM : M.Nonsymplectic)
    (d : ExtensionBorels.CompatibleBorelData s T K (MonoidHom.id M.Carrier) M.U M.B) :
    False :=
  exclude_of_root_centralizers s T K ha hz hDN hac han hzn hER
    (borelCandidate s T K) d.placement (catalogue_root_centralizers s T K M hM d)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
