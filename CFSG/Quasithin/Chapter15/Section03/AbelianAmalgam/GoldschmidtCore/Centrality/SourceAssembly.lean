module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.AdequateRankOne
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Consumer
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.InitialAssembly
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.KnownSimple

/-!
# The original-source centrality clause and terminal application

The earlier line structure and the original I₀ descent provide the Baumann
control, cubic residual, escaping two-perfect factor and local core identity.
Conjugate the latter by the original s to obtain the first amalgam core
identity before constructing any record containing centrality. The enumerated
fusion inputs give the required singular intersections in the same pulled-back
quadratic form. The adequate good-or-bad reduction and the independent pushing-up
exclusion then prove O₂(H) ≤ C_G(V), hence the literal V ≤ Z(O₂(H)).

The resulting proof fills OriginalSource.SourceData.centrality and feeds its
terminal contradiction. No recognized model, extra fusion conclusion, or
centrality-bearing source record is an input. Corrected F.6, adequate B.5 and the
doubled-natural specialization of C.1.37 remain explicit universal source
inputs, as do the genuine earlier local, I₀ descent and fusion data.

Source: Aschbacher–Smith, 15.3.46, 15.3.66–68 and the final proof of 15.3.1,
printed pp.1141 and 1152–1155; the repaired centrality route uses C.1.37.
-/

public section

open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly

open Semilinear
open CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace FullSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E)
    (hs : s ∈ planeStabilizer T P) (hsE : s ∉ lineT T E)
    (c : TerminalConfiguration T M (residualY M Mc) (localModule T M)
      E (otherLine E s) earlier.natural)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (classificationF : Recognition.FSource.SourceClassificationInput κ)
    (classificationB : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ)
    (doubled : PushingUp.DoubledNaturalSource κ)

local notation "V" => localModule T M
local notation "Y" => residualY M Mc
local notation "F₀" => otherLine E s
local notation "D" => lineT (T : Subgroup G) E
local notation "H" => OriginalSource.sourceGroup T M Mc E s
local notation "A₁" => firstAmalgamGroup Y (T : Subgroup G) E F₀

include earlier descent hs hsE c fusion hG classificationF classificationB doubled

/-- Source 15.3.68(2), in the centralizer form consumed by the original-source
terminal record. The original earlier inputs and universal classifiers are
retained; every bad-character module and transport premise is discharged. -/
theorem core_centralizes_of_source :
    twoCoreAmbient H ≤ centralizer (V : Set G) := by
  let := OriginalSource.standard_elementary earlier.natural
  let r := LocalStructure.initialStructure earlier
  have hTM : (T : Subgroup G) ≤ M := earlier.ordering.1.2
  have hYM : Y ≤ M := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hTM.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc))
  obtain ⟨hCT,hMprod,hGEprod,_hYN,_hXN,_hXq,⟨eB⟩,hXM,_hGEq,hXJ⟩ :=
    Descent.source_descent descent
  have hCTT : centralizer (V : Set G) ≤ (T : Subgroup G) := hCT.le.trans inf_le_left
  have hCD : centralizer (V : Set G) ≤ D :=
    le_inf hCTT ((centralizer_le earlier.line_le).trans (Subgroup.centralizer_le_normalizer _))
  have hcB : Nat.card (lineY Y E ⧸ localTwoCore (lineY Y E)) = 3 := by
    rw [localTwoCore_eq_pCore]
    exact (Nat.card_congr eB.toEquiv).trans (by simp [Nat.card_eq_fintype_card])
  have hXJ' : lineX E = ⁅lineX E, elementaryAbelianMaxJ D⁆ := by
    rw [descent.thompson_eq]
    exact hXJ
  obtain ⟨_,hindex,_,_,hZE,_⟩ := Orthogonal.line_sylow_geometry_of_source
    earlier.natural T P E hTM earlier.plane_le earlier.plane_card
    earlier.plane_definite earlier.line_le earlier.line_card earlier.line_singular
    earlier.central_fixed earlier.selected earlier.selected_map
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [earlier.other_centralizer]
    exact le_centralizer_iff.mp (earlier.central_fixed.le.trans inf_le_right)

  -- Conjugate the original 66(5) identity. No SourceData is constructed here.
  have hYF : lineY Y F₀ = otherLine (lineY Y E) s :=
    GoldschmidtCore.lineY_otherLine Y E s (hTY hs.1)
  have hTmap : (T : Subgroup G).map (MulAut.conj s⁻¹).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp
      ((T : Subgroup G).le_normalizer ((T : Subgroup G).inv_mem hs.1))
  have hDmap : (D).map (MulAut.conj s⁻¹).toMonoidHom = D := by
    rw [lineT, map_inf _ _ _ (MulAut.conj s⁻¹).injective, hTmap,
      map_equiv_normalizer_eq]
    exact c.lineT_eq
  have hYmap : (lineY Y E).map (MulAut.conj s⁻¹).toMonoidHom = lineY Y F₀ :=
    hYF.symm
  have h66F : twoCoreAmbient A₁ = A₁ ⊓ centralizer (F₀ : Set G) := by
    have h := congrArg (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom) descent.local_core
    rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj s⁻¹).injective,
      Subgroup.map_sup, hDmap, hYmap,
      map_inf _ _ _ (MulAut.conj s⁻¹).injective,
      Subgroup.map_sup, hDmap, hYmap, OriginalSource.centralizer_map_equiv] at h
    exact h

  have hdef := OriginalSource.definite_of_standard earlier.natural
    earlier.plane_le earlier.plane_card earlier.plane_definite
  have h46all := FusionCore.lemma_15_3_46_of_earlier_inputs
    (OriginalSource.quadraticAction earlier.natural) fusion hdef
  have h46 : ∀ g : G, g ∉ M → ∀ v : V,
      (v : G) ∈ (V).map (MulAut.conj g).toMonoidHom → earlier.natural.singular v := by
    intro g hg v hv
    apply (OriginalSource.quadraticAction_singular earlier.natural v).mp
    exact (h46all.2.1.1 g hg).2 v ⟨v.property,hv⟩
  let := earlier.local_span_abelian
  rcases AdequateRankOne.FullSource.terminal_good_or_bad_module hG classificationF classificationB
      T M Mc Y V E F₀ earlier.natural c hTM hYM earlier.line_le earlier.line_card
      earlier.line_singular hZE earlier.central_card earlier.residual_image
      earlier.residual_core_module hCTT h66F hcB hXM hXJ' rfl hMprod hindex hTMc
      h46 hGEprod r.span_le_local s hs.1 hsE with hgood | ⟨_hUVE,hbad⟩
  · exact hgood
  · exact (BadCharacterReduction.excluded hG doubled H (lineY Y E) A₁ D V
      (conjugateSpanBy V H) M (lineX E) c.normalizes_lineY s hbad hcB
      (le_sup_left.trans le_sup_right) (lineX_twoPerfect E) hXM
      (r.baumann_le.trans inf_le_right) hCD r.characteristic_control
      descent.maximal_two_local).elim

/-- The literal centrality conclusion of 15.3.68(2) for the original amalgam,
with the center mapped along the inclusion of its actual ambient two-core. -/
theorem module_le_center_of_source :
    V ≤ (center (twoCoreAmbient H)).map (twoCoreAmbient H).subtype := by
  have hc := core_centralizes_of_source earlier descent hs hsE c fusion hG
    classificationF classificationB doubled
  have hVC : V ≤ centralizer (twoCoreAmbient H : Set G) := le_centralizer_iff.mp hc
  intro v hv
  refine mem_map.mpr ⟨⟨v,c.module_le_core hv⟩,?_,rfl⟩
  apply mem_center_iff.mpr
  intro q
  exact Subtype.ext (mem_centralizer_iff.mp (hVC hv) q q.property)

/-- Construct the existing original-source terminal input after proving its
centrality field. This uses exactly the original s, F and earlier action. -/
noncomputable def originalSourceData : OriginalSource.SourceData T M Mc P E s where
  earlier := earlier
  descent := descent
  conjugator_mem := hs
  conjugator_outside := hsE
  terminal := c
  centrality := core_centralizes_of_source earlier descent hs hsE c fusion hG
    classificationF classificationB doubled

/-- Actual application to the final 15.3.1 consumer. Only the genuine earlier
local/descent/fusion data and full F.6, adequate B.5 and doubled-natural C.1.37
source implications remain. The ambient SQTK restriction and the terminal
adequate-FF witness are constructed on the original groups and actions. -/
theorem terminal_contradiction_of_source : False := by
  let d := originalSourceData earlier descent hs hsE c fusion hG
    classificationF classificationB doubled
  let _ := OriginalSource.standard_elementary earlier.natural
  let k := d.coordinateModel
  let g := d.earlierGeometry k
  have h := SourceControls.controls_of_earlier_fusion_inputs k g fusion d.source_definite
    d.terminal.support_M d.residual_escape
  have hB : TerminalRecognition.Intersection.SourceFFClassificationInput.{u,u} κ := by
    intro A _ _ W _ _ ρ hyp
    cases classificationB A W ρ hyp with
    | trivial h => exact Or.inl (.trivial h)
    | quasisimple hq ha => exact Or.inl (.quasisimple hq ha)
    | symmetricThree h => exact Or.inl (.symmetricThree h)
    | twoFactors h => exact Or.inl (.twoFactors h)
    | outerSixThree h => exact Or.inr ⟨h⟩
    | hyperplane h => exact Or.inl (.hyperplane h)
  exact terminal_contradiction_of_source_ambient_span g h (d.sourceGroup_sqtk hG)
    classificationF hB d.seed_le_original d.source_span

end FullSource

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E)
    (hs : s ∈ planeStabilizer T P) (hsE : s ∉ lineT T E)
    (c : TerminalConfiguration T M (residualY M Mc) (localModule T M)
      E (otherLine E s) earlier.natural)
    (fusion : FusionCore.EarlierFusionInputs T M (localModule T M) P)
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (classificationF : Recognition.FSource.ClassificationInput κ)
    (classificationB : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} κ)
    (doubled : PushingUp.DoubledNaturalSource κ)

local notation "V" => localModule T M
local notation "Y" => residualY M Mc
local notation "F₀" => otherLine E s
local notation "D" => lineT (T : Subgroup G) E
local notation "H" => OriginalSource.sourceGroup T M Mc E s
local notation "A₁" => firstAmalgamGroup Y (T : Subgroup G) E F₀

include earlier descent hs hsE c fusion hG classificationF classificationB doubled

/-- Compatibility with the original public F input. -/
theorem core_centralizes_of_source :
    twoCoreAmbient H ≤ centralizer (V : Set G) :=
  FullSource.core_centralizes_of_source earlier descent hs hsE c fusion hG
    classificationF.adequate.source classificationB doubled

/-- Compatibility with the original public F input and literal center map. -/
theorem module_le_center_of_source :
    V ≤ (center (twoCoreAmbient H)).map (twoCoreAmbient H).subtype :=
  FullSource.module_le_center_of_source earlier descent hs hsE c fusion hG
    classificationF.adequate.source classificationB doubled

/-- The original public constructor retains its earlier data and centrality. -/
noncomputable def originalSourceData : OriginalSource.SourceData T M Mc P E s :=
  FullSource.originalSourceData earlier descent hs hsE c fusion hG
    classificationF.adequate.source classificationB doubled

/-- Compatibility with the original terminal consumer. -/
theorem terminal_contradiction_of_source : False :=
  FullSource.terminal_contradiction_of_source earlier descent hs hsE c fusion hG
    classificationF.adequate.source classificationB doubled

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.SourceAssembly
