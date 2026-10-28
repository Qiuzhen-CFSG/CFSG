module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointQuasisimpleComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointImageEquality
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointXiComplete
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointSylowSwap
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointSylowTransport
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointPairs

/-!
# Original tensor point normality in the generation-one branch

At a nonsingular point with the original Sylow placement, failure of
normality gives a strict normal containing C-component. The actual
quasisimple catalogue excludes the quasisimple case. The central Sylow
geometry supplies the characteristic-two join and its reduced Omega orbit,
which contains the diagonal moved subgroup and the original tensor line.
The completed FF argument identifies the two action images; the source Xi
contradiction then excludes the strict component.

The original generation-one hypothesis supplies the factor-swapping element
inside the literal point Sylow centralizer. The same original H is retained
throughout. Sylow conjugacy in M transports normality to every nonsingular
point, and the original pair-centralizer and corank-three applications follow.

Source: Aschbacher--Smith 9.4.1--3, printed pp.735--736, in the n(H)=1 branch.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Source 9.4.1 in the generation-one branch, with its original outside
maximal-local guard and the actual H-star subgroup retained. -/
theorem tensorPointResidual_normality_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H₀ : Subgroup G} (hH : H₀ ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H₀ = 1)
    (v : D.fullModule) (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G) := by
  apply m.tensorPointResidual_normality_of_sylow_points ?_ v hv
  intro w hw hs
  by_contra hn
  obtain ⟨I,hLI,hIX,hI,hIN,_⟩ := m.tensorPointResidual_strict_component_source w hw hn
  have hq := m.tensorPoint_containing_not_quasisimple w hw hLI.le hIX hIN
  let X := I ⊔ ((T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G))
  let U := conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) I
  let W := U.subgroupOf X
  have hr : IsPReduced 2 W :=
    m.tensorPoint_centerOrbit_reduced_source w hw hLI.le hIX hI hIN hq hs
  let := hr.normal
  obtain ⟨hAU,hline⟩ := m.tensorPoint_centerOrbit_contains_geometry w hw hs hLI.le
  have heU : W.map X.subtype = U := map_subgroupOf_eq_of_le
    ((m.tensorPoint_centerOrbit_le_containing hout w hw hs hLI.le).trans le_sup_left)
  have heq := m.tensorPoint_centerOrbit_image_eq w hw hLI.le hIX hI hIN hs hr hAU
  obtain ⟨t,ht,htL⟩ := m.exists_point_sylow_swap_of_generation_one hout hH hgen w hw hs
  exact m.tensorPoint_Xi_contradiction_of_image_eq w hw hLI hIX hI hIN hs W
    (by rw [heU]; exact hAU) (by rw [heU]; exact hline) heq t ht htL

/-- Source 9.4.2 on the original pair of nonsingular field lines. -/
theorem tensor_pair_centralizer_le_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1)
    (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hw : ((m.sectionData.coordinates w).toAdd).det ≠ 0)
    (hne : (m.sectionData.coordinates w).toAdd ∉
      Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)) :
    centralizer ({(v : G),(w : G)} : Set G) ≤ D.maximalLocal :=
  m.tensor_pair_centralizer_le_of_point_normality
    (m.tensorPointResidual_normality_of_generation_one hout hH hgen) v w hv hw hne

include m in
/-- Source 9.4.3 for the original full module in the same generation-one branch. -/
theorem tensor_globalR_gt_three_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) : 3 < ChapterE.globalR D.fullModule :=
  m.tensor_globalR_gt_three_of_point_normality
    (m.tensorPointResidual_normality_of_generation_one hout hH hgen)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
