module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorCorankPreparation
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorHyperplaneSylow
public import Theory.Representation.OrthogonalFourPlusMatrix.HyperplaneFixed

/-!+# The original field-four tensor corank bound

An escaping hyperplane can be conjugated inside M so that its Sylow
normalizer has the required local index. Its image in the determinant
module then has a Sylow stabilizer whose fixed space lies in that image.
Lifting this Sylow subgroup through the original component quotient gives
C_V(N_T(U)) ≤ U. The proved Omega-center escape E.6.10(4) contradicts
9.2.2, which puts the same Omega center in C_V(N_T(U)). Thus r(G,V) ≥ 2.

The actual H-star generation bound consequently gives w(T,V) ≤ 1 when
n(H)=1. This supplies the numerical side of the remaining 9.4 exclusion;
the independent point-centralizer and weak-closure arguments must still
contradict that upper bound.

Source: Aschbacher--Smith 9.2.3 and 9.4, printed pp.730 and 735--737.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterE.Section06 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

/-- Source 9.2.3 in the field-four tensor branch, with no fixed-space premise. -/
theorem globalR_ge_two_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal) :
    2 ≤ globalR D.fullModule := by
  apply le_of_not_gt
  intro hr
  have hr1 : globalR D.fullModule = 1 :=
    le_antisymm (ENat.lt_two_iff.mp hr) (one_le_globalR D.fullModule)
  obtain ⟨U,hUV,he,hc⟩ := globalR_attained (by rw [hr1]; simp)
  have hc1 : subgroupCorank D.fullModule U = 1 := by
    exact_mod_cast hc.trans hr1
  have heM : ¬ centralizer (U : Set G) ≤ D.maximalLocal := by
    rwa [source_fullModule_normalizer D] at he
  obtain ⟨W,hWV,hcW,heW,hiW⟩ :=
    m.tensor_hyperplane_normalizer_choice hUV hc1 heM
  apply m.tensor_hyperplane_fixed_control_false hout hWV hcW heW
  apply m.fullModule_centralizer_le_of_stabilizer_sylow_fixed W hWV hiW
  apply Binary.HyperplaneFixed.fixedSpace_sylow_le
  have hd := (m.sectionData.imageSpace W).finrank_quotient_add_finrank
  rw [m.tensor_hyperplane_image_finrank hWV hcW,Binary.finrank_binary] at hd
  omega

/-- The original generation-one H-star group forces the weak-closure
parameter to be at most one; the corank alternative is discharged internally. -/
theorem weakClosure_le_one_of_generation_one
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hgen : generationParameter H = 1) :
    globalW D.fullModule (T : Subgroup G) ≤ 1 := by
  have hb := source_overgroup_generation_bound D hH.1.1.2 hH.1.2
    (show 0 < generationParameter H by omega)
  rw [hgen,Nat.cast_one] at hb
  rcases min_le_iff.mp hb with hw | hr
  · exact hw
  · exact (not_le_of_gt (by norm_num : (1 : ℕ∞) < 2)
      ((m.globalR_ge_two_source hout).trans hr)).elim

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
