module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorCorankPreparation
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPairs

/-!
A binary subspace of the field-four determinant module with codimension at
most three contains nonsingular vectors on two different field lines.
Transporting this result through the original subgroup coordinates reduces
source 9.4.3 to the pair-centralizer conclusion of 9.4.2. The final theorem
retains exactly that independent point-centralizer input.

Source: Aschbacher--Smith, 9.4.2--3, printed p.736.
-/

public section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterE.Section06 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
variable {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
include m

theorem corank_le_three_nonsingular_pair {U : Subgroup G}
    (hUV : U ≤ D.fullModule) (hc : subgroupCorank D.fullModule U ≤ 3) :
    ∃ v w : D.fullModule, (v : G) ∈ U ∧ (w : G) ∈ U ∧
      ((m.sectionData.coordinates v).toAdd).det ≠ 0 ∧
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 ∧
      (m.sectionData.coordinates w).toAdd ∉
        Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V) := by
  let := m.fullModule_elementary
  have hi : U.relIndex D.fullModule = 2 ^ subgroupCorank D.fullModule U := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact D.fullModule.relIndex_eq_two_pow_quotient_finrank U
  have hd := m.sectionData.imageSpace_codimension_of_index U hUV bot_le _ hi
  rw [Binary.finrank_binary] at hd
  have hdim : 4 < Module.finrank (ZMod 2) (m.sectionData.imageSpace U) := by omega
  obtain ⟨x,hx,y,hy,hxd,hyd,hxy⟩ := Binary.exists_nonsingular_pair_of_finrank_gt_four
    (m.sectionData.imageSpace U) hdim
  obtain ⟨v,hv,rfl⟩ := (m.sectionData.mem_imageSpace_iff U x).mp hx
  obtain ⟨w,hw,rfl⟩ := (m.sectionData.mem_imageSpace_iff U y).mp hy
  exact ⟨v,w,hv,hw,hxd,hyd,hxy⟩

theorem small_corank_centralizer_of_nonsingular_pair_control
    (hpair : ∀ v w : D.fullModule,
      ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 →
      (m.sectionData.coordinates w).toAdd ∉
        Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V) →
      centralizer ({(v : G), (w : G)} : Set G) ≤ D.maximalLocal)
    {U : Subgroup G} (hUV : U ≤ D.fullModule)
    (hc : subgroupCorank D.fullModule U ≤ 3) :
    centralizer (U : Set G) ≤ D.maximalLocal := by
  obtain ⟨v,w,hv,hw,hvn,hwn,hne⟩ := m.corank_le_three_nonsingular_pair hUV hc
  apply le_trans _ (hpair v w hvn hwn hne)
  apply centralizer_le
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | h
  · exact hv
  · exact (Set.mem_singleton_iff.mp h) ▸ hw


theorem globalR_gt_three_of_nonsingular_pair_control
    (hpair : ∀ v w : D.fullModule,
      ((m.sectionData.coordinates v).toAdd).det ≠ 0 →
      ((m.sectionData.coordinates w).toAdd).det ≠ 0 →
      (m.sectionData.coordinates w).toAdd ∉
        Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V) →
      centralizer ({(v : G), (w : G)} : Set G) ≤ D.maximalLocal) :
    3 < globalR D.fullModule := by
  by_contra hn
  have hr : globalR D.fullModule ≤ 3 := le_of_not_gt hn
  obtain ⟨U,hUV,he,hc⟩ := globalR_attained (ne_top_of_le_ne_top (by simp) hr)
  have hc3 : subgroupCorank D.fullModule U ≤ 3 := by
    exact_mod_cast hc.trans_le hr
  have heM : ¬ centralizer (U : Set G) ≤ D.maximalLocal := by
    rwa [source_fullModule_normalizer D] at he
  exact heM (m.small_corank_centralizer_of_nonsingular_pair_control hpair hUV hc3)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
