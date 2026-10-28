module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalSymplecticExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5PairCatalogue.Symplectic

/-!
# The original A₅ context excludes the native reduced symplectic comparison

The binary endpoints are solvable. At every larger field degree, the actual
reduced endpoint map identifies the original factor with its native local
factor. The original chosen module excludes either native radical lattice.
The subgroup in the F.1.1 pair is arbitrary and is preserved throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
open ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric.Global.OriginalSymplectic
open Theory.SpecificGroups.SymplecticFour A5PairCatalogue SuzukiContainment
variable {G : Type*} [Group G] [Finite G]
  {A : Fin 2 → Subgroup G} {S : Subgroup G}

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
theorem original_context_not_reduced_symplectic
    {T : Sylow 2 G} {L K V V₁ V₂ V₃ : Subgroup G}
    (d : Context T L V V₁ V₂ V₃)
    (h : HypothesisF11 ![L,K] S)
    (a : ∀ i, Nonempty ((![L,K] i ⧸ pCore 2 (![L,K] i)) ≃*
      alternatingGroup (Fin 5)))
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
    exact overgroup_not_solvable 0 (a 0).some (le_sup_left.trans le_sup_left)
      (Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective)
  obtain ⟨e⟩ := local_symplectic_equiv h 0 d.quotient F hF hn' b c.left
  cases b
  · exact original_context_not_symplectic_plane_local_equiv d F hF hn' e
  · exact original_context_not_symplectic_point_local_equiv d F hF hn' e

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
