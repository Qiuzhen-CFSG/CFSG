module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.ResidualMarking
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Symplectic

/-!
# Reduced symplectic recognition at the original selected pair

The native lift and the preserved reduced residuals construct both full
original endpoint markings. The normalized-Borel consumer then places the
same original S in the selected R and removes the outer extension. Its field
and natural-block conclusions use the actual original quotient markings.
In this consumer the binary field is excluded by embedding the nonsolvable
selected factor in a solvable binary parabolic, before invoking native lifting.

Source: DGS (1985), (15.2), printed pp.226–228; Aschbacher–Smith F.1.12,
pp.263–264, and 5.2.6, pp.650–651. Reduced recognition remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open Chapter6.Source.RankOneGeneric Theory.SpecificGroups.SymplecticFour

/-- Restore the full original marking from the reduced one. Perfectness of
the selected factors is not needed for this residual transport. -/
theorem exists_original_symplectic_marking_of_reduced_iso
    {G : Type*} [Group G] {L R S : Subgroup G} (h : HypothesisF11 ![L,R] S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 1 < m) (point : Bool)
    (e : Iso (reducedAmalgam ![L,R] S) (SymplecticNative.amalgam F point)) :
    Nonempty (Global.OriginalSymplectic.Marking F point L R S) := by
  obtain ⟨E,f,hl,hr,_⟩ := SymplecticNative.exists_original_extension_iso F h hF hm point e
  have hres (b : Bool) :
      (solvableResidual (SymplecticNative.endpoint F b)).map
        (SymplecticNative.endpoint F b).subtype = Global.OriginalSymplectic.localFactor F b := by
    cases b
    · exact planeParabolic_solvableResidual_eq hF hm
    · exact pointParabolic_solvableResidual_eq hF hm
  have hf := residualMarkingOfRestoredIso h E f e.left e.right hl hr
  rw [hres point,hres (!point)] at hf
  exact ⟨hf⟩

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Global.Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m) (point : Bool)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) (SymplecticNative.amalgam F point))
include d h hTH hp hm hF e

omit [CharP F 2] in
/-- The original nonsolvable selected factor already excludes the binary
reduced row; no original marking is used to justify the native lift. -/
theorem symplectic_reduced_parameter : 1 < m := by
  by_contra hgt
  have hm1 : m = 1 := by omega
  have hc : Nat.card F = 2 := by simpa only [hm1,pow_one] using hF
  let P := Source.parabolic ![L,R]
    (SuzukiContainment.reducedSylow ![L,R] (Global.sourceS L H)) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let a : SymplecticNative.endpoint F (!point) ≃* Binary.LocalProduct := by
    cases point
    · exact Binary.pointParabolicEquivProd hc
    · exact Binary.planeParabolicEquivProd hc
  let j := a.toMonoidHom.comp (e.right.toMonoidHom.comp (inclusion hRP))
  have hj : Function.Injective j :=
    a.injective.comp (e.right.injective.comp (inclusion_injective hRP))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 2)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable R := Group.isSolvable_of_isSolvable_injective hj
  exact d.parabolics_not_solvable h hp 1
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient 1).mpr (by
      change Group.IsSolvable (R ⧸ pCore 2 R)
      infer_instance))

/-- The original normalized Borel places the original S in the same selected
R and hence adjoining S leaves its original two-core unchanged. -/
theorem symplectic_original_core_and_containment_of_reduced_iso :
    (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R := by
  obtain ⟨f⟩ := exists_original_symplectic_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) F hF (symplectic_reduced_parameter d h hTH hp F hm hF point e) point e
  have hs := d.sourceS_le_right_of_original_symplectic h hTH hp F hm hF point f
  exact ⟨by rw [sup_eq_left.mpr hs],hs⟩

/-- The same restored maps give both inclusion squares of the original pure
comparison and identify the field and the two natural blocks. -/
theorem symplectic_original_comparison_of_reduced_iso :
    Nonempty (Iso (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H))
      (Global.OriginalSymplectic.orientedAmalgam F point)) ∧
      m = n ∧ 1 < m ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n := by
  obtain ⟨f⟩ := exists_original_symplectic_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) F hF (symplectic_reduced_parameter d h hTH hp F hm hF point e) point e
  exact ⟨⟨d.originalSymplecticComparison h hTH hp F hm hF point f⟩,
    d.original_symplectic_field_and_blocks h hTH hp F hm hF point f⟩

/-- Discharge the original-marking premise at the concrete catalogue consumer. -/
theorem concreteComparison_of_reduced_symplectic :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨f⟩ := exists_original_symplectic_marking_of_reduced_iso
    (d.hypothesisF11 h hTH) F hF (symplectic_reduced_parameter d h hTH hp F hm hF point e) point e
  exact d.concreteComparison_of_original_symplectic h hTH hp F hm hF point f

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
