module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeNumerical
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeChiefImage
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLineFFComplete
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.PSL3FourChiefExclusion

/-!
# The original old residual has A₅ quotient

In the only alternative PSL₃(4) branch, the tensor action has quadratic
ratio at least4/3 and its dual is non-FF. The genuine qrc and local
uniqueness arguments therefore select a noncentral chief factor of the
actual H-conjugate span with ratio at most two. Its action kernel is O₂(H),
so its faithful image is an SQTK group with normal PSL₃(4) residual and
two-group quotient. The irreducible chief-action exclusion gives ratio
strictly greater than two, a contradiction.

Thus the literal embedded O²(H) has A₅ as its two-core quotient. The final
consumers remove the PSL₃(4) premise from the four-field overgroup theorem
and the residual-model premise from the nonzero Cartan-core line theorem.
The original nonzero-core and Cartan/line inputs are retained where needed;
the zero-core amalgam branch is separate.

Source: Aschbacher--Smith9.2.7 and9.3.1--3, printed pp.731--734, with the
chief-factor numerical argument in3.1.6 and D.1.3(b).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterD ChapterD.UniqueFactor ChapterE
open ChapterC.MSCentralOrbit ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- The original PSL₃(4) residual alternative is impossible. -/
theorem old_residual_linear_three_false
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4) : False := by
  obtain ⟨hU,hs⟩ := m.old_residual_linear_three_exists_small_chief_of_tensor hH hlarge hK hm
  let := hU
  obtain ⟨s,i,hi,hq⟩ := hs
  let σ := s.factorRepresentation i
  let := s.factorRepresentation_irreducible i
  let K := (pResidual 2 H).map (actionHom σ)
  let : K.Normal := Normal.map inferInstance (actionHom σ) σ.asGroupHom.rangeRestrict_surjective
  obtain ⟨hsq,hmodel,_,_,hquot,hcore⟩ :=
    m.old_residual_linear_three_chief_image_structure hH hlarge hK hm s i hi
  exact (not_lt_of_ge hq)
    (ChapterK.Linear.Recognition.PSL3FourExclusion.quadraticRatio_gt_two_of_irreducible
      (ρ := Representation.BinaryOffender.imageRepresentation σ) (L := K)
      hsq hmodel hquot hcore (Representation.BinaryOffender.imageRepresentation_injective σ)
      (imageRepresentation_irreducible σ inferInstance))

/-- The literal embedded old residual has A₅ as its two-core quotient. -/
theorem old_residual_a5
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H) :
    Nonempty (((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5)) :=
  m.old_residual_a5_of_no_linear_three_four hH hlarge
    (fun hK _ hm => m.old_residual_linear_three_false hH hlarge hK hm)

/-- The original four-field overgroup consumer has no PSL₃(4) exclusion premise. -/
theorem old_residual_overgroup_fourField_models_of_source_recognition
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G)) :
    m.tensorLine ≤ M₀.pCoreIn 2 ∧ M₀ ∈ Chapter1.He G ∧
      generalizedFitting M₀ = pCore 2 M₀ ∧ center M₀ = ⊥ ∧
    let R := ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀
    let W := omegaOrbit R
    ∃ hr : IsPReduced 2 W,
      let := hr.normal; letI := hr.elementary
      let ρ : Representation (ZMod 2) (ActionQuotient W) (Additive W) := action W
      let N := offenderSubgroup ρ
      m.tensorLine.subgroupOf M₀ ≤ W ∧
      (pResidual 2 M₀).map (actionMk W) ≤ N ∧
      ChapterB.QuasisimpleSource.moved (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) = ⊤ ∧
      ∃ h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        (ρ.comp N.subtype) (((pResidual 2 M₀).map (actionMk W)).subgroupOf N),
      SourceA5TensorExclusion.FourWayFourField (ρ.comp N.subtype)
        (((pResidual 2 M₀).map (actionMk W)).subgroupOf N) h.sectionData :=
  m.old_residual_overgroup_fourField_models_of_no_linear_three_four hH hlarge
    (fun hK _ hm => m.old_residual_linear_three_false hH hlarge hK hm)
    houtside M₀ hcore hgen hKU

/-- The nonzero Cartan-core branch centralizes the original line without a residual model premise. -/
theorem old_residual_centralizes_tensorLine_of_nonzero_cartan_core_of_tensor
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G) := by
  obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
  exact m.old_residual_centralizes_tensorLine_of_nonzero_cartan_core hH eK A B
    hAB hA9 hAe hB3 hBC hcore

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
