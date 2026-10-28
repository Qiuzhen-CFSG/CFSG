module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Preparation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearFlags
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.BinaryMarked
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.FullSylow
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.OmegaAction.SourceAction
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.BinarySource
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.BinaryExclusion

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.SourceActions
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMarking
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.MSPreparation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.LinearThreeMS
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.AlternatingPlacement
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.Remaining
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSymplectic
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingExceptional

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingNonSix

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSmall
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingAlternating
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingPermutation
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.SourceRemaining
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingNatural
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingMarked
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.RemainingSeven
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSeven
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.OriginalSevenExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSevenExclusion

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.Catalogue.CubicSymplecticExclusion

/-!
# The original escaping-component contradiction

The preparation constructs the literal C.2.3 input, C.2.6 Fitting-preimage
containment and escaping C-component. The original Omega action supplies
NI = C_M(Z1), its index-six action with kernel C_NI(V), and the point
marking. C.2.4 then normalizes the same component under the original radical.
The unrestricted B.5.1 reduction retains that component, its whole moved
section, the actual actions and the original parabolic markings.

The linear-three rows are excluded using their full core models and the
original NI action. Corrected SmallActionsSource excludes the binary L₄/L₅
rows with all local seed and action premises discharged. The symplectic,
G₂, triple-six, five-letter and exceptional seven-letter calculations
remove the other rows. Legacy APIs requiring EarlierMSClassifications
remain conditional; its refuted universal field is not used in this source
contradiction.

OriginalSeven identifies U = [⟨ZS^X⟩,X] with the full moved subgroup.
Its actual conjugation action and the original QI Thompson-normalizer
control exclude both central covers of the seven-letter row. The remaining
row is the marked binary symplectic A₆ action with cubic core center.

CubicSymplecticExclusion closes that row using the original C.2.6
containment. Relative normality puts the central core preimage of X inside
NI. Rank two puts its cubic image in the image of K, contradicting
K ∩ M = O₂(K). This yields the component contradiction directly, with no
new KS-placement hypothesis. The same selected component and full moved
section are used throughout.

The final CharacteristicTwo.Source module combines this contradiction with
the proved no-chi and NI ≤ MI exclusions to establish original 15.2.23.
The earlier HStar quotients, Kc orbit, restricted actions and plane inverter
retain their original producers and final plane-uniqueness discharge.

Source: Aschbacher--Smith, 15.2.18--23, printed pp.1113--1117,
C.2.4--7, pp.144--147; refs/quasithin.pdf.
-/
