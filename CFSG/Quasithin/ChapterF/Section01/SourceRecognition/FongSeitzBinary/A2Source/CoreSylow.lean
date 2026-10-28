module
public import Theory.GroupTheory.PCoreInRestriction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.NaturalCore
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.NormalGeneration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneCenters

/-!
# The original common Sylow is the product of the two natural cores

Each full parabolic core lies in the original F.1.1 Sylow S. The genuine
b=1 natural actions make their product a Sylow in the full parabolic, so
maximality identifies the product with S itself. Its image is exactly the
specified split unipotent group, using the literal original quotient map.

Source: DGS, Groups and Graphs, 10.5, printed p.156; AS F.1.1--3.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open DGS85 DGS85.NoncommutingProfile Subgroup.CosetGeometry.RankTwo
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace ProjectiveCoordinates
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (h : HypothesisF11 L S)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance coreSylowFieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (fullFamily L S) (base (fullFamily L S) false)
    (base (fullFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (fullFamily L S) (base (fullFamily L S) true)
    (base (fullFamily L S) false) k₁ W₁)

include h in
/-- Each original full parabolic core lies in the original common Sylow. -/
theorem original_core_le_sylow (i : Bool) :
    Q (fullFamily L S) (base (fullFamily L S) i) ≤ S.subgroupOf (generated L S) := by
  simp only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base]
  cases i
  · change (((parabolic L S 0).subgroupOf (generated L S)).pCoreIn 2) ≤ _
    rw [pCoreIn_subgroupOf 2 _ _ (parabolic_le_generated 0)]
    exact comap_mono (h.parabolic_core_le_S 0)
  · change (((parabolic L S 1).subgroupOf (generated L S)).pCoreIn 2) ≤ _
    rw [pCoreIn_subgroupOf 2 _ _ (parabolic_le_generated 1)]
    exact comap_mono (h.parabolic_core_le_S 1)

include h c₀ c₁ in
/-- The two actual natural cores generate the literal original common Sylow. -/
theorem original_core_sup_eq_sylow :
    Q (fullFamily L S) (base (fullFamily L S) false) ⊔
      Q (fullFamily L S) (base (fullFamily L S) true) = S.subgroupOf (generated L S) := by
  let P := (parabolic L S 0).subgroupOf (generated L S)
  let T := Q (fullFamily L S) (base (fullFamily L S) false) ⊔
    Q (fullFamily L S) (base (fullFamily L S) true)
  have hTS : T ≤ S.subgroupOf (generated L S) :=
    sup_le (original_core_le_sylow h false) (original_core_le_sylow h true)
  obtain ⟨R,hR⟩ := (paired_core_product_sylow h.generatedLocallyRankOneTriple c₀ c₁).1
  change (R : Subgroup P).map P.subtype = T at hR
  have hSP : S.subgroupOf (generated L S) ≤ P :=
    comap_mono (le_sup_right.trans le_sup_left)
  have hRS : (R : Subgroup P) ≤ (S.subgroupOf (generated L S)).subgroupOf P := by
    intro x hx
    apply hTS
    rw [←hR]
    exact mem_map_of_mem P.subtype hx
  have he := R.is_maximal' ((h.S_isP.comap_subtype).comap_subtype) hRS
  change (S.subgroupOf (generated L S)).subgroupOf P = (R : Subgroup P) at he
  have hh := congrArg (Subgroup.map P.subtype) he
  rw [map_subgroupOf_eq_of_le hSP,hR] at hh
  exact hh.symm

include h c₀ c₁ in
/-- The same quotient map identifies that core product with its specified U. -/
theorem original_core_sup_image (d : SourceQuotient L S) (split : SplitData d.tits) :
    (Q (fullFamily L S) (base (fullFamily L S) false) ⊔
      Q (fullFamily L S) (base (fullFamily L S) true)).map d.q = split.U := by
  rw [original_core_sup_eq_sylow h c₀ c₁]
  exact quotient_sourceS_image_eq_unipotent h d split

end ProjectiveCoordinates
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
