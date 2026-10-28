module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorSection
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.SmallModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.BinaryAction
public import Theory.GroupTheory.PCoreNormalizerAction.Frattini
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer

/-!
# Nonnormal point-centralizer models and the invariant factorization

The original cubic Sylow has dihedral automizer of order eight. The concrete
linear-three and Mathieu-eleven Sylow-pair calculations therefore exclude
both rows for the actual normal closure K_z. Its remaining invariant rows
are PSL₄(2), PSL₅(2), and the adequate Held alternative. For these rows the
outer group is a two-group. Residual recovery and the original Sylow then
give G_z = K_z N_{G_z}(X); the proved normalizer containment yields the exact
product G_z = K_z M_z. The binary rows also give the full automorphism
quotient of the original K_z T by its own two-core.

Only intrinsic local results from Chapter15 are reused; no later global
source theorem is assumed. The original cubic Sylows, relative normality,
and literal two-core quotient maps are preserved. Swapped-row analysis,
Held exclusion, tensor recognition and both quiet exclusions remain with
the selected-module owner. Source: Aschbacher--Smith 8.3.7, pp.724--725,
with the adequate Held alternative retained from original 1.3.4.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
open Chapter1.XiEmbedding
open Chapter15.Section04.LocalSetup.EmbeddingReduction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- The intrinsic embedding input for every original cubic Sylow. -/
theorem quiet_tensor_point_localInput
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    LocalInput 3 (T : Subgroup G) d.X ((P : Subgroup d.X).map d.X.subtype) d.Gz := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXi := quiet_tensor_point_residual_mem_Xi D hn e hbase hzV hz1 hzT
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient d.X) := by
    refine Or.inl ⟨IsElementaryAbelian.of_injective c.toMonoidHom c.injective,?_⟩
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  exact Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hT
    (sup_le (d.X_le.trans inf_le_right) hzT) (by decide) hq P

/-- The actual D₈ automizer excludes the L₃(3) covers and M₁₁ for K_z. -/
theorem quiet_tensor_point_invariant_exclusions
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    ¬ LinearThreeModel 3 (Chapter1.XiQuotient d.Kz) ∧
      ¬ Nonempty (Chapter1.XiQuotient d.Kz ≃* Sporadic.Mathieu.M11) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hD := quiet_tensor_point_automizer_dihedral D hn e hbase hzV hz1 hzT P
  exact ⟨SmallModels.not_linearThreeModel hi hT d.Kz_le_Gz d.Kz_normal d.X_le_Kz hD,
    SmallModels.not_mathieuEleven hi hT d.Kz_le_Gz d.Kz_normal d.X_le_Kz hD⟩

/-- The detected orbit after the original normal and small-model exclusions. -/
theorem quiet_tensor_point_normalClosure_models
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let P₀ := (P : Subgroup d.X).map d.X.subtype
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn d.Gz ∧ IsQuasisimple (Chapter1.XiQuotient K) ∧
      d.Kz = componentOrbit K (T : Subgroup G) ∧ ⁅d.Kz,P₀⁆ = d.Kz ∧
      Nonempty (P₀ ≃* Plane 3) ∧
      ((SwappedFactors (T : Subgroup G) P₀ K ∧ SwappedModel 3 (Chapter1.XiQuotient K)) ∨
        (d.Kz = K ∧
          (ClassicalGroup.IsPSL (Chapter1.XiQuotient K) 4 2 ∨
            ClassicalGroup.IsPSL (Chapter1.XiQuotient K) 5 2 ∨
            Nonempty (Chapter1.XiQuotient K ≃* Held.He)))) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨K,hK,hq,hclosure,hcomm,hP,hrows⟩ :=
    quiet_tensor_point_normalClosure_component D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
  refine ⟨K,hK,hq,hclosure,hcomm,hP,?_⟩
  rcases hrows with hs | ⟨hTK,hr⟩
  · exact Or.inl hs
  have he : d.Kz = K := hclosure.trans
    (le_antisymm (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) K le_rfl hTK)
      (le_componentOrbit K (T : Subgroup G)))
  have hx := quiet_tensor_point_invariant_exclusions D hn e hbase hzV hz1 hzT P
  change ¬ LinearThreeModel 3 (Chapter1.XiQuotient d.Kz) ∧
    ¬ Nonempty (Chapter1.XiQuotient d.Kz ≃* Sporadic.Mathieu.M11) at hx
  rw [he] at hx
  refine Or.inr ⟨he,?_⟩
  rcases hr with hl | (hm | h4 | h5) | hh
  · exact (hx.1 hl).elim
  · exact (hx.2 hm).elim
  · exact Or.inl h4
  · exact Or.inr (Or.inl h5)
  · exact Or.inr (Or.inr hh)

private theorem model_outer_two {Q : Type*} [Group Q] [Finite Q]
    (hm : ClassicalGroup.IsPSL Q 4 2 ∨ ClassicalGroup.IsPSL Q 5 2 ∨
      Nonempty (Q ≃* Held.He)) : IsPGroup 2 (MulAut.Outer Q) := by
  rcases hm with h4 | h5 | hh
  · have hb := BinaryAction.binary_outer_card_le_two (Or.inl rfl) h4
    have hp : 0 < Nat.card (MulAut.Outer Q) := Nat.card_pos
    have hc : Nat.card (MulAut.Outer Q) = 1 ∨ Nat.card (MulAut.Outer Q) = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa using hc)
    · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc)
  · have hb := BinaryAction.binary_outer_card_le_two (Or.inr rfl) h5
    have hp : 0 < Nat.card (MulAut.Outer Q) := Nat.card_pos
    have hc : Nat.card (MulAut.Outer Q) = 1 ∨ Nat.card (MulAut.Outer Q) = 2 := by omega
    rcases hc with hc | hc
    · exact IsPGroup.of_card (p := 2) (n := 0) (by simpa using hc)
    · exact IsPGroup.of_card (p := 2) (n := 1) (by simpa using hc)
  · obtain ⟨e⟩ := hh
    have hp : IsPGroup 2 (MulAut.Outer Held.He) :=
      Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
        Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient
    exact hp.of_injective (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective

/-- Two-group outer action gives the exact original point-centralizer product. -/
theorem quiet_tensor_point_factor_of_outer_two
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (ho : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      IsPGroup 2 (MulAut.Outer (Chapter1.XiQuotient d.Kz))) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.Gz : Set G) = (d.Kz : Set G) * (d.Mz : Set G) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hcoreH : d.Gz.pCoreIn 2 ≤ normalizer (d.X : Set G) := by
    rw [←hi.residual]
    exact le_sup_left.trans (le_normalizer_embedded_pResidual 2 _)
  have hcore : d.Kz.pCoreIn 2 ≤ normalizer (d.X : Set G) :=
    (pCoreIn_mono_of_normalizes d.Kz_le_Gz (le_normalizer_conjugateSpanBy _ _)).trans hcoreH
  have hf := relative_residual_normalizer_factor d.Gz d.Kz d.X (T.subtype hzT)
    d.Kz_le_Gz d.Kz_normal d.X_le_Kz hi.perfect hcore
    (by
      change ((T : Subgroup G).subgroupOf d.Gz).map d.Gz.subtype ≤ normalizer (d.X : Set G)
      rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ d.Gz from hzT)]
      exact hi.invariant) ho
  have hNM := quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT
  have hNM' : d.Gz ⊓ normalizer (d.X : Set G) ≤ d.Mz := by
    change d.Gz ⊓ normalizer (d.X : Set G) ≤ D.maximalLocal ⊓ d.Gz
    exact le_inf hNM inf_le_left
  have he : d.Kz ⊔ d.Mz = d.Gz := by
    apply le_antisymm (sup_le d.Kz_le_Gz inf_le_right)
    exact hf.ge.trans (sup_le le_sup_left (hNM'.trans le_sup_right))
  have hnorm : d.Gz ≤ normalizer (d.Kz : Set G) := le_normalizer_conjugateSpanBy _ _
  exact (congrArg (fun A : Subgroup G => (A : Set G)) he).symm.trans
    (coe_mul_of_right_le_normalizer_left d.Kz d.Mz (inf_le_right.trans hnorm))

/-- The invariant surviving model rows discharge the outer-action premise. -/
theorem quiet_tensor_point_invariant_factor
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (hm : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      ClassicalGroup.IsPSL (Chapter1.XiQuotient d.Kz) 4 2 ∨
      ClassicalGroup.IsPSL (Chapter1.XiQuotient d.Kz) 5 2 ∨
      Nonempty (Chapter1.XiQuotient d.Kz ≃* Held.He)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (d.Gz : Set G) = (d.Kz : Set G) * (d.Mz : Set G) :=
  quiet_tensor_point_factor_of_outer_two D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
    (model_outer_two hm)

/-- The original K_z T two-core quotient is the full binary automorphism group. -/
theorem quiet_tensor_point_binary_quotient
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {n : ℕ} (hn' : n = 4 ∨ n = 5)
    (hm : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      ClassicalGroup.IsPSL (Chapter1.XiQuotient d.Kz) n 2) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    Nonempty (Chapter1.XiQuotient d.KzT ≃* MulAut (Chapter1.XiQuotient d.Kz)) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  exact BinaryAction.binary_quotient_aut_of_local hi hT d.Kz_le_Gz d.Kz_normal d.X_le_Kz hn' hm

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
