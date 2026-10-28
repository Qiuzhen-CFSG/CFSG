module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Linear
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores

/-!
# Elementary original cores in the native linear A₅ row

The same reduced endpoint map identifies each original factor with the
native parabolic solvable residual. These point and line locals are actual
special affine groups, so their two-cores are elementary translation planes.
The proved unrestricted linear join-core equality then gives elementary
cores of the original LᵢS, without normalizing an original Borel or bounding
the field. All original core embeddings are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.A5PairNativeLinear
open DGS85.OriginalExtension Matrix.PSL3 Matrix.PSL3.LinearThree
open SourceCompletion.LinearThreeEven A5PairCatalogue SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem linear_model_residual (F : Type) [Field F] [Finite F]
    (hc : 4 ≤ Nat.card F) (b : Bool) :
    (solvableResidual (SmallCompletion.parabolic F b)).map
      (SmallCompletion.parabolic F b).subtype = OuterExtensions.localFactor F (!b) := by
  cases b
  · exact ParabolicResiduals.pointParabolic_residual F hc
  · exact ParabolicResiduals.lineParabolic_residual F hc

private theorem linear_model_core_le_residual (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool) :
    pCore 2 (SmallCompletion.parabolic F b) ≤
      solvableResidual (SmallCompletion.parabolic F b) := by
  let P := SmallCompletion.parabolic F b
  let K := OuterExtensions.localFactor F (!b)
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
  have hr : (solvableResidual P).map P.subtype = K := linear_model_residual F hc b
  have hKP : K ≤ P := hr ▸ map_subtype_le _
  have hnP : P ≤ normalizer (K : Set PSL(3,F)) := by
    rw [←hr]
    simpa only [normalizer_eq_top, ←MonoidHom.range_eq_map, range_subtype] using
      (solvableResidual P).le_normalizer_map P.subtype
  have hh := OuterExtensions.AmbientLocalCores.local_join_core_in_aut
    F (by omega : 0<n) hF (!b) (P.map MulAut.conj) (by
      rintro a ⟨x,hx,rfl⟩
      exact mem_normalizer_iff_map_conj_eq.mp (hnP hx))
  have hcore : (K ⊔ P).pCoreIn 2 = K.pCoreIn 2 := by
    apply map_injective (Matrix.PSL3.ExtensionBorel.inner_injective F)
    rw [map_pCoreIn_of_injective 2 _ _ (Matrix.PSL3.ExtensionBorel.inner_injective F),
      map_pCoreIn_of_injective 2 _ _ (Matrix.PSL3.ExtensionBorel.inner_injective F), Subgroup.map_sup]
    exact hh
  rw [sup_eq_right.mpr hKP] at hcore
  apply (map_le_map_iff_of_injective P.subtype_injective).mp
  change P.pCoreIn 2 ≤ _
  rw [hr,hcore]
  exact map_subtype_le _

private theorem local_affine_equiv
    (h : HypothesisF11 L S) (i : Fin 2)
    (a : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool)
    (e : parabolic L (reducedSylow L S) i ≃* SmallCompletion.parabolic F b) :
    Nonempty (L i ≃* Matrix.SL2.Affine F) := by
  let P := parabolic L (reducedSylow L S) i
  let M := SmallCompletion.parabolic F b
  let f : L i →* PSL(3,F) := M.subtype.comp
    (e.toMonoidHom.comp (inclusion (show L i ≤ P from le_sup_left.trans le_sup_left)))
  have hf : Function.Injective f := M.subtype_injective.comp
    (e.injective.comp (inclusion_injective _))
  have hc : 4 ≤ Nat.card F := by
    rw [hF]
    exact (show 2^2 ≤ 2^n from Nat.pow_le_pow_right (by decide) hn)
  have hm := local_marking_of_reduced_equiv h i a e
    (linear_model_core_le_residual F hF hn b)
  have hr : f.range = OuterExtensions.localFactor F (!b) := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range]
    rw [hm]
    exact linear_model_residual F hc b
  let E := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  cases b
  · exact ⟨E.trans (pointLocalEquivAffine F)⟩
  · exact ⟨E.trans (lineLocalEquivAffine F)⟩

/-- Every original whole join core in a native linear comparison is elementary.
The comparison preserves the entire reduced Borel; no Borel normalization
or restriction on the original core order is assumed. -/
theorem linear_join_cores_elementary
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (e : Iso (reducedAmalgam L S) (LinearNative.amalgam F b)) :
    ∀ i, IsElementaryAbelian 2 (twoCore (L i ⊔ S)) := by
  have hn' := linear_parameter a F hF hn b e
  have hcore := linear_join_cores h a F hF hn' b e
  intro i
  have haff : Nonempty (L i ≃* Matrix.SL2.Affine F) := by
    fin_cases i
    · exact local_affine_equiv h 0 (a 0).some F hF hn' b e.left
    · exact local_affine_equiv h 1 (a 1).some F hF hn' (!b) e.right
  obtain ⟨E⟩ := haff
  let Ec : pCore 2 (L i) ≃* Matrix.SL2.translations F :=
    ((pCore 2 (L i)).equivMapOfInjective E.toMonoidHom E.injective).trans
      (MulEquiv.subgroupCongr ((pCore_map_iso 2 E).trans (Matrix.SL2.affine_twoCore_eq F)))
  let : IsElementaryAbelian 2 (pCore 2 (L i)) :=
    IsElementaryAbelian.of_injective Ec.toMonoidHom Ec.injective
  rw [hcore i]
  exact IsElementaryAbelian.map _

end CFSG.Quasithin.ChapterF.Source.A5PairNativeLinear
