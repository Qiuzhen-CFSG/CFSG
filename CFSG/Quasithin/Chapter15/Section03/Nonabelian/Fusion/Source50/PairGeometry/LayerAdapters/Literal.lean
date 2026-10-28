module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Source
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.NaturalPair
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure.QuotientCentralizer.Reduction

/-!
# Source (54) adapters on the original Chapter 15 subgroups

The source witness, its common multiplicity, and the canonical quotient
model are kept together. Transport to the literal pair I, core P, module V,
and residual Y preserves that multiplicity. Once the independent source
recognition proves s = 1, these constructors supply both layer-action
fields consumed by Fusion.Assembly.EarlierData. The given quadratic
marking is preserved through the exact lower-coordinate formula.

The earlier G.2.6 hypotheses and the independent s = 1 proof remain with
the original-source assembly; no action alignment is an extra premise.
Source: Aschbacher–Smith, 15.3.54 and 15.3.58–60, printed pp.1146,1148–1150.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
open scoped IsMulCommutative
open Subgroup Core.Automizers Core.Automizers.Models Cubic.MLocal.Structure
open CFSG.Quasithin.ChapterG.Section02
open Setup OrthogonalPlusFour
open OrthogonalPlusFour.Chapter15Assembly OrthogonalPlusFour.Chapter15Collapse
open OrthogonalPlusFour.Multiplicity
open Representation.BinaryQuadraticPair InvertedCubicTensor
variable {G : Type*} [Group G] [Finite G]

def castLayers {I Y P V I' Y' P' V' : Subgroup G}
    {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
    [(V.subgroupOf P).Normal] [(V'.subgroupOf P').Normal]
    (r : LayerActions I Y P V hIP hIV)
    (hI : I = I') (hY : Y = Y') (hP : P = P') (hV : V = V')
    (hIP' : I' ≤ normalizer (P' : Set G)) (hIV' : I' ≤ normalizer (V' : Set G)) :
    LayerActions I' Y' P' V' hIP' hIV' := by
  subst I' Y' P' V'
  exact r

omit [Finite G] in
theorem castLayers_lowerEquiv {I Y P V I' Y' P' V' : Subgroup G}
    {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
    [(V.subgroupOf P).Normal] [(V'.subgroupOf P').Normal]
    (r : LayerActions I Y P V hIP hIV)
    (hI : I = I') (hY : Y = Y') (hP : P = P') (hV : V = V')
    (hIP' : I' ≤ normalizer (P' : Set G)) (hIV' : I' ≤ normalizer (V' : Set G)) :
    (castLayers r hI hY hP hV hIP' hIV').lowerCoordinates =
      (MulEquiv.subgroupCongr hV).symm.trans r.lowerCoordinates := by
  subst I' Y' P' V'
  rfl

def transportLayers {I Y P V I' Y' P' V' : Subgroup G}
    {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
    [(V.subgroupOf P).Normal] [(V'.subgroupOf P').Normal]
    (r : LayerActions I Y P V hIP hIV)
    (hI : I = I') (hY : Y = Y') (hP : P = P') (hV : V = V')
    (hIP' : I' ≤ normalizer (P' : Set G)) (hIV' : I' ≤ normalizer (V' : Set G)) :
    LayerActions I' Y' P' V' hIP' hIV' :=
  { castLayers r hI hY hP hV hIP' hIV' with
    lowerCoordinates := (MulEquiv.subgroupCongr hV).symm.trans r.lowerCoordinates
    lower_compatible := by
      intro i v
      simpa only [castLayers_lowerEquiv] using
        (castLayers r hI hY hP hV hIP' hIV').lower_compatible i v }

omit [Finite G] in
theorem transportLayers_lower {I Y P V I' Y' P' V' : Subgroup G}
    {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
    [(V.subgroupOf P).Normal] [(V'.subgroupOf P').Normal]
    (r : LayerActions I Y P V hIP hIV)
    (hI : I = I') (hY : Y = Y') (hP : P = P') (hV : V = V')
    (hIP' : I' ≤ normalizer (P' : Set G)) (hIV' : I' ≤ normalizer (V' : Set G)) (v : V) :
    (transportLayers r hI hY hP hV hIP' hIV').lowerCoordinates
      (MulEquiv.subgroupCongr hV v) = r.lowerCoordinates v := by
  change r.lowerCoordinates ((MulEquiv.subgroupCongr hV).symm (MulEquiv.subgroupCongr hV v)) = _
  rw [MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem transport_leftMultiplicity {I P V Y I' P' V' Y' : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : FactorData I P V Y W)
    (hI : I = I') (hP : P = P') (hV : V = V') (hY : Y = Y') :
    (f.transport hI hP hV hY).decomposition.leftMultiplicity =
      f.decomposition.leftMultiplicity := by
  subst I' P' V' Y'
  rfl

omit [Finite G] in
theorem transport_rightMultiplicity {I P V Y I' P' V' Y' : Subgroup G}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : FactorData I P V Y W)
    (hI : I = I') (hP : P = P') (hV : V = V') (hY : Y = Y') :
    (f.transport hI hP hV hY).decomposition.rightMultiplicity =
      f.decomposition.rightMultiplicity := by
  subst I' P' V' Y'
  rfl

variable {M Z ZS Zperp V Y T : Subgroup G} {g : G}

theorem literalCanonicalSource (a : NaturalOrthogonalAction M V) (hTM : T ≤ M)
    (hSyl : ∃ P : Sylow 2 M, (P : Subgroup M).map M.subtype = T)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g) :
    letI := moduleSectionNormal d d.I_eq_LU
    letI := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
    ∃ f : SourceModuleData d,
      f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity := by
  let := moduleSectionNormal d d.I_eq_LU
  let := moduleSectionElementary d d.I_eq_LU d.S_normalizes_U d.S_eq_coreProduct
  obtain ⟨f⟩ := d.source_module_data
  exact ⟨f, f.common_of_factorExchange
    (Chapter15Exchange.literal_factorExchange a hTM hSyl hspan d)⟩

variable [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
  ((Chapter15.setup Z Zperp Y T).S g)).Normal]
  [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]

def literalCanonicalFactorData (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z) :
    FactorData (pairI Z ZS g) (pairP Z ZS g) V Y
      (Additive (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)) :=
  (canonicalFactorData d f (by
    change omegaCenter T ≤ (Chapter15.setup Z Zperp Y T).VL
    rw [hΩ]
    exact point_le_VL (Chapter15.setup Z Zperp Y T))).transport (Chapter15.I_eq g hZS hperp)
      (Chapter15.S_eq g hZS hperp) (Chapter15.VL_eq hspan) rfl

theorem literalCanonicalFactorData_multiplicity
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z) :
    (literalCanonicalFactorData hZS hperp hspan d f hΩ).decomposition.leftMultiplicity =
      f.decomposition.leftMultiplicity :=
  transport_leftMultiplicity _ _ _ _ _

theorem literalCanonicalFactorData_common
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    (literalCanonicalFactorData hZS hperp hspan d f hΩ).decomposition.leftMultiplicity =
      (literalCanonicalFactorData hZS hperp hspan d f hΩ).decomposition.rightMultiplicity := by
  have hr : (literalCanonicalFactorData hZS hperp hspan d f hΩ).decomposition.rightMultiplicity =
      f.decomposition.rightMultiplicity := transport_rightMultiplicity _ _ _ _ _
  exact (literalCanonicalFactorData_multiplicity hZS hperp hspan d f hΩ).trans
    (hsame.trans hr.symm)

theorem literalCanonicalSource_core_card
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    Nat.card (pairP Z ZS g) = 2 ^ (4 * f.decomposition.leftMultiplicity + 4) := by
  rw [← Chapter15.S_eq (Y := Y) (T := T) g hZS hperp]
  apply canonicalFactorData_core_card d f _ hsame
  change omegaCenter T ≤ _
  rw [hΩ]
  exact point_le_VL (Chapter15.setup Z Zperp Y T)

def literalLayersOfSourceData (a : NaturalOrthogonalAction M V)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    (hIM : pairI Z ZS g ≤ M) [(V.subgroupOf (pairP Z ZS g)).Normal] :
    LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V
      (pairI_normalizes_pairP Z ZS g) (hIM.trans a.normalizes) := by
  have : (((Chapter15.setup Z Zperp Y T).VL).subgroupOf
      ((Chapter15.setup Z Zperp Y T).S g)).Normal := by
    rw [Chapter15.VL_eq hspan, Chapter15.S_eq g hZS hperp]
    infer_instance
  have hΩD : omegaCenter (Chapter15.setup Z Zperp Y T).T ≤
      (Chapter15.setup Z Zperp Y T).VL := by
    change omegaCenter T ≤ _
    rw [hΩ]
    exact point_le_VL (Chapter15.setup Z Zperp Y T)
  exact transportLayers (layersOfSourceData d f hΩD hsame hone)
    (Chapter15.I_eq g hZS hperp) rfl (Chapter15.S_eq g hZS hperp)
    (Chapter15.VL_eq hspan) _ _

def literalNaturalPairOfSourceData (a : NaturalOrthogonalAction M V)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    (hIM : pairI Z ZS g ≤ M) [(V.subgroupOf (pairP Z ZS g)).Normal] :
    NaturalQuotientPair a (pairI Z ZS g) (pairP Z ZS g) hIM (pairI_normalizes_pairP Z ZS g) :=
  naturalPairOfLayers (literalLayersOfSourceData a hZS hperp hspan d f hΩ hsame hone hIM) a hIM

theorem literalLayersOfSourceData_lower (a : NaturalOrthogonalAction M V)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    (hIM : pairI Z ZS g ≤ M) [(V.subgroupOf (pairP Z ZS g)).Normal]
    (v : (Chapter15.setup Z Zperp Y T).VL) :
    (literalLayersOfSourceData a hZS hperp hspan d f hΩ hsame hone hIM).lowerCoordinates
      (MulEquiv.subgroupCongr (Chapter15.VL_eq hspan) v) =
        determinantToTensor (d.coordinates v) := by
  change determinantToTensor (d.coordinates
    ((MulEquiv.subgroupCongr (Chapter15.VL_eq hspan)).symm
      (MulEquiv.subgroupCongr (Chapter15.VL_eq hspan) v))) = _
  rw [MulEquiv.symm_apply_apply]

theorem literalLayersOfSourceData_determinant (a : NaturalOrthogonalAction M V)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V) (d : OrthogonalPlusFour.Hypothesis (Chapter15.setup Z Zperp Y T) g)
    (f : SourceModuleData d) (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity)
    (hone : f.decomposition.leftMultiplicity = 1)
    (hIM : pairI Z ZS g ≤ M) [(V.subgroupOf (pairP Z ZS g)).Normal]
    (v : (Chapter15.setup Z Zperp Y T).VL) :
    ClassicalOrthogonal.FourPlusMatrix.determinantForm
      ((literalLayersOfSourceData a hZS hperp hspan d f hΩ hsame hone hIM).lowerCoordinates
        (MulEquiv.subgroupCongr (Chapter15.VL_eq hspan) v)).toAdd =
          ClassicalOrthogonal.FourPlusMatrix.determinantForm (d.coordinates v).toAdd := by
  rw [literalLayersOfSourceData_lower]
  exact determinantToTensor_determinant _

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
