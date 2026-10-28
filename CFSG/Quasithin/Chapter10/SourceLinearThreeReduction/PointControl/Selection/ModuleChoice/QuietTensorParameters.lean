module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorFull
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound
public import Theory.Representation.BinaryTensorThree.FixedCodimension

/-!
# The original binary tensor weak-closure parameters

The coordinates on the full ambient automizer transfer the checked lower
bound on involution displacement; the swapping involution attains three.
Thus m(G,V)=3. The Fundamental Setup supplies the literal E.6.1 hypotheses,
so the proved known-simple E.6.3 theorem gives r(G,V) ≥ 3 and s(G,V)=3.
This establishes 8.3.2 on the original recognized tensor row.

The weak-closure application retains the same S=O₂(XT) and every original
nonidentity Sylow-fixed point. Tensor irreducibility also removes a separate
full/local equality or cubic-divisibility premise. The stronger r>3 of
8.3.11, point-core inclusion of 8.3.12, base-action recognition, both quiet
tensor exclusions and FixedSupportRowsAt remain with the selected-module
owner. Final point-control assembly remains with its existing owner.
Source: Aschbacher--Smith E.6.3, 8.3.2 and 8.3.11--14,
printed pp.245,723,726--727.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem fullModule_hypothesisE61 :
    Section06.HypothesisE61 KnownSimple.IsKnownSimple T D.maximalLocal D.fullModule := by
  have hu := D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_sup_right.trans hu.2.1
  have hVN := D.maximalLocal_normalizes_fullModule
  have hVT := D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)
  refine ⟨D.simpleQTKE,hu.1,hTM,?_,inferInstance,hVT,
    (normal_subgroupOf_iff_le_normalizer hVT).mpr (hTM.trans hVN),?_,?_⟩
  · intro he
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq he))
  · intro g hg
    exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hVN hg))
  · intro N hN hle
    apply hu.2.2 N hN
    apply le_trans _ hle
    exact le_inf (le_inf hu.2.1 (hu.2.1.trans hVN))
      (source_join_normalizes_full_sylow_centralizer D (source_module_nonsolvable_uniqueness D))

/-- The source minimum displacement is three for the actual ambient automizer. -/
theorem quiet_tensor_localM_eq_three
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    localM D.fullModule = 3 := by
  obtain ⟨f,hf⟩ := quiet_tensor_automizer_coordinates D hn e hbase
  let ρ := automizerRepresentation D.fullModule
  have hc (t : Automizer D.fullModule) :
      fixedCodim ρ (zpowers t) = fixedCodim BinaryTensorThree.action (zpowers (f t)) := by
    have hh := fixedCodim_map_equivariant ρ BinaryTensorThree.action f.toMonoidHom e hf (zpowers t)
    simpa only [MonoidHom.map_zpowers,MulEquiv.coe_toMonoidHom] using hh
  apply le_antisymm
  · have ht : orderOf (f.symm BinaryTensorThree.swap) = 2 :=
      (f.symm.orderOf_eq _).trans BinaryTensorThree.orderOf_swap
    have hh := moduleM_le_involution ρ ht
    rw [hc,f.apply_symm_apply,BinaryTensorThree.fixedCodim_swap] at hh
    exact hh
  · change 3 ≤ moduleM ρ
    unfold moduleM
    apply le_csInf ⟨_,Set.mem_insert _ _⟩
    rintro n (rfl | ⟨t,ht,rfl⟩)
    · rw [e.finrank_eq]
      rw [Module.finrank_matrix]
      norm_num
    · rw [hc]
      exact BinaryTensorThree.involution_fixedCodim_ge_three (f t) ((f.orderOf_eq t).trans ht)

/-- Original 8.3.2: the genuine E.6.3 theorem gives r ≥ 3 and s = 3.
This does not assert the strictly stronger r > 3 of 8.3.11. -/
theorem quiet_tensor_source_parameters
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range) :
    localM D.fullModule = 3 ∧ (3 : ℕ∞) ≤ globalR D.fullModule ∧
      globalS D.fullModule = 3 := by
  have hm := quiet_tensor_localM_eq_three D hn e hbase
  have h := Section06.FrobeniusReduction.lower_bound_knownSimple (fullModule_hypothesisE61 D)
    (by rw [hm]; decide)
  exact ⟨hm,by simpa [hm] using h.1,
    by simpa [hm] using h.2.1⟩

/-- Apply the source parameter and full/local-module equalities to the literal
weak-closure subgroup. Only tensor-base recognition, point-core containment
and the strict r bound remain; no cubic-divisibility premise is required. -/
theorem quiet_tensor_source_weakClosure_two
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hcore : D.fullModule ≤ (centralizer ({z} : Set G)).pCoreIn 2)
    (hr : (3 : ℕ∞) < globalR D.fullModule) :
    globalS D.fullModule = 3 ∧
      indexedWeakClosure D.fullModule
        (Chapter8.Section03.CentralizerSetup.S ⟨T,localOrbit T L,z⟩) 2 ≤
          centralizer (D.fullModule : Set G) := by
  refine ⟨(quiet_tensor_source_parameters D hn e hbase).2.2,?_⟩
  apply quiet_tensor_weakClosure_two_of_orbit_image D hn _ e hbase hzV hz1 hzT hcore hr
  rwa [quiet_tensor_fullModule_eq_module D e hbase]

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
