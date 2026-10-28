module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalLinearExclusion
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSymplecticExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Linear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Symplectic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.IntrinsicBOne.Recognition
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Theory.SpecificGroups.PSL3.SmallCompletion.Orders

/-!
# The original left A₅ context excludes the noncommuting b=1 branch

The left component's actual A₅ quotient excludes the binary linear and
symplectic endpoints. In larger fields, the same reduced endpoint map
identifies that component with the native residual. The original chosen
module excludes the affine and symplectic local factors.

Intrinsic DGS recognition supplies one of those comparisons from the
unchanged critical-pair, noncommuting and b=1 hypotheses. The right factor
and the subgroup S remain arbitrary throughout; no right quotient marking,
normalized Borel, or classification callback is required.

Source: DGS, Groups and Graphs (1985), Chapters 7, 10 and 14, and
Aschbacher--Smith F.1.12(I)(1--2), printed pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
open ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.DGS85
open ChapterF.Source.DGS85.Reduction ChapterF.Source.DGS85.Assembly
open A5PairCatalogue SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {A : Fin 2 → Subgroup G} {S : Subgroup G}

section Linear
open Matrix.PSL3 Matrix.PSL3.LinearThree
open ChapterF.SourceCompletion.LinearThreeEven
variable {L : Fin 2 → Subgroup G}

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


/-- A left original A₅ context excludes the native reduced linear row,
with no quotient marking on the right factor. -/
theorem original_context_not_reduced_linear_of_left
    {T : Sylow 2 G} {L K V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,K] S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (c : Iso (reducedAmalgam ![L,K] S) (LinearNative.amalgam F b)) : False := by
  have hn' : 1<n := by
    by_contra hgt
    have hn1 : n = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    have ht := CartanActions.BorelQuotient.card_torus_mul_scalar F
    norm_num [hc] at ht
    have hmodel : Nat.card (SmallCompletion.parabolic F b) = 24 := by
      rw [SmallCompletion.card_parabolic F hF b,hc,ht]
      norm_num
    let P := parabolic ![L,K] (reducedSylow ![L,K] S) 0
    have hP : Nat.card P = 24 := (Nat.card_congr c.left.toEquiv).trans hmodel
    have h60 : 60 ∣ Nat.card L := by
      have hd := card_quotient_dvd_card (pCore 2 L)
      rw [Nat.card_congr d.quotient.toEquiv,nat_card_alternatingGroup] at hd
      norm_num [Nat.factorial] at hd
      exact hd
    have hd := h60.trans (card_dvd_of_le
      (show L ≤ P from le_sup_left.trans le_sup_left))
    rw [hP] at hd
    norm_num at hd
  obtain ⟨e⟩ := local_affine_equiv h 0 d.quotient F hF hn' b c.left
  exact original_context_not_affine_equiv d F e

end Linear

section Symplectic
open Chapter6.Source.RankOneGeneric.Global.OriginalSymplectic
open Theory.SpecificGroups.SymplecticFour

private theorem symplectic_model_residual
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool) :
    (solvableResidual (SymplecticNative.endpoint F b)).map
      (SymplecticNative.endpoint F b).subtype = localFactor F b := by
  cases b
  · exact planeParabolic_solvableResidual_eq hF hn
  · exact pointParabolic_solvableResidual_eq hF hn

private theorem symplectic_model_core_le_residual
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool) :
    pCore 2 (SymplecticNative.endpoint F b) ≤
      solvableResidual (SymplecticNative.endpoint F b) := by
  cases b
  · change pCore 2 (planeParabolic (F := F)) ≤ solvableResidual (planeParabolic (F := F))
    apply (map_le_map_iff_of_injective planeParabolic.subtype_injective).mp
    rw [planeParabolic_solvableResidual_eq hF hn,←planeLocal_core_map]
    exact map_subtype_le _
  · change pCore 2 (pointParabolic (F := F)) ≤ solvableResidual (pointParabolic (F := F))
    apply (map_le_map_iff_of_injective pointParabolic.subtype_injective).mp
    rw [pointParabolic_solvableResidual_eq hF hn,←pointLocal_core_map]
    exact map_subtype_le _

private theorem local_symplectic_equiv
    (h : HypothesisF11 A S) (i : Fin 2)
    (a : (A i ⧸ pCore 2 (A i)) ≃* alternatingGroup (Fin 5))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1<n) (b : Bool)
    (e : parabolic A (reducedSylow A S) i ≃* SymplecticNative.endpoint F b) :
    Nonempty (A i ≃* localFactor F b) := by
  let P := parabolic A (reducedSylow A S) i
  let M := SymplecticNative.endpoint F b
  let f : A i →* Sp F := M.subtype.comp
    (e.toMonoidHom.comp (inclusion (show A i ≤ P from le_sup_left.trans le_sup_left)))
  have hf : Function.Injective f := M.subtype_injective.comp
    (e.injective.comp (inclusion_injective _))
  have hm := local_marking_of_reduced_equiv h i a e
    (symplectic_model_core_le_residual F hF hn b)
  have hr : f.range = localFactor F b := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,hm]
    exact symplectic_model_residual F hF hn b
  exact ⟨(MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)⟩

/-- No native reduced symplectic row has an original A₅ context at its left endpoint. -/
theorem original_context_not_reduced_symplectic_of_left
    {T : Sylow 2 G} {L K V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,K] S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0<n) (b : Bool)
    (c : Iso (reducedAmalgam ![L,K] S) (SymplecticNative.amalgam F b)) : False := by
  have hn' : 1<n := by
    by_contra hgt
    have hn1 : n = 1 := by omega
    have hc : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    let f : SymplecticNative.endpoint F b ≃* Binary.LocalProduct := by
      cases b
      · exact Binary.planeParabolicEquivProd hc
      · exact Binary.pointParabolicEquivProd hc
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 2)) := Group.isSolvable_of_comm (by decide)
    let j := c.left.trans f
    exact overgroup_not_solvable 0 d.quotient (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  obtain ⟨e⟩ := local_symplectic_equiv h 0 d.quotient F hF hn' b c.left
  cases b
  · exact original_context_not_symplectic_plane_local_equiv d F hF hn' e
  · exact original_context_not_symplectic_point_local_equiv d F hF hn' e

end Symplectic

/-- The actual critical noncommuting b=1 branch is incompatible with the
original left A₅ Context, for an arbitrary right factor and subgroup S. -/
theorem original_context_critical_bOne_impossible
    {T : Sylow 2 G} {L K V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,K] S)
    {v w : Vertex (reducedFamily ![L,K] S)}
    (hc : IsCriticalPair (reducedFamily ![L,K] S) v w)
    (hne : ⁅Z (reducedFamily ![L,K] S) v,Z (reducedFamily ![L,K] S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily ![L,K] S) = 1) : False := by
  obtain ⟨F,_,_,_,n,hn,hF,he⟩ :=
    IntrinsicBOne.small_comparison_of_critical_bOne h hc hne hb
  rcases he with ⟨point,⟨e⟩⟩ | ⟨point,⟨e⟩⟩
  · exact original_context_not_reduced_linear_of_left d h F hF hn point e
  · exact original_context_not_reduced_symplectic_of_left d h F hF hn point e

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
