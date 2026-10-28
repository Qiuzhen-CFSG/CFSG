module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearFlagTransport
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalA2MarkedRecognition
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink

/-!
# The accepted marked A₂ recognition in the concrete linear catalogue

Transport the entire flag amalgam to a small copy of its source field.
Finite binary dimension supplies a positive degree and the exact field
cardinality. Both orientations then give the literal `.linear` row,
including fields of orders two and four and the full scalar quotient.

The Chapter 12 application consumes the accepted original marked A₂
recognition, retaining its natural actions, whole-Borel normalization,
module coordinates, centerfreeness and rotation-order-three premises.
These remain with their genuine earlier source producers. This closes
catalogue packaging of the selected A₂ branch; minimality and exhaustive
selection of the seven rows remain with source assembly.
Source: DGS Theorem D, p.224; Aschbacher--Smith 12.2.2 and F.1.12(I)(1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source
open Matrix.PSL3.RootPresentationRecognition
open Chapter6.Source.RankOneGeneric.Global GreenBook
variable {A B C : Type*} [Group A] [Group B] [Group C]
  {α : RankTwoAmalgam A B C}

theorem linear_catalogue_of_flagIso {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (e : RankTwoAmalgam.Iso α (flagAmalgam F i)) :
    ConcreteAmalgamComparison α := by
  let k : F ≃+* Shrink.{0} F := (Shrink.ringEquiv.{0,_} F).symm
  let K := Shrink.{0} F
  let : CharP K 2 := (k.toRingHom.charP_iff_charP 2).mp inferInstance
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hc : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
  apply ConcreteAmalgamComparison.linear K (Module.finrank (ZMod 2) K) Module.finrank_pos hc
  let d := e.trans (flagFieldIso k i)
  fin_cases i
  · exact Or.inl ⟨d⟩
  · exact Or.inr ⟨d⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.A2Source

open Subgroup Theory.GroupTheory Configuration
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Matrix.PSL3.RootPresentationRecognition
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.Source
open ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85 ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance a2CatalogueFieldAlgebra {K : Type*} [Field K] [CharP K 2] :
    Algebra (ZMod 2) K := ZMod.algebra K 2

include D in
theorem rankOne_a2_concrete_source_comparison
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {H A B R : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (prep : Global.Preparation T L H A B R)
    {X : Type*} [Group X] {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)
    (mark : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic ![L,R] (Global.sourceS L H) 0)
        (parabolic ![L,R] (Global.sourceS L H) 0 ⊓ parabolic ![L,R] (Global.sourceS L H) 1)
        (parabolic ![L,R] (Global.sourceS L H) 1) inf_le_left inf_le_right) d.standardAmalgam)
    (split : SplitData d.tits)
    (c₀ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true) k₀ W₀)
    (c₁ : BOneActionData (fullFamily ![L,R] (Global.sourceS L H))
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) true)
      (CosetGeometry.base (fullFamily ![L,R] (Global.sourceS L H)) false) k₁ W₁)
    (hn₀ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₀.actor : Set _))
    (hn₁ : (commonBorel ![L,R] (Global.sourceS L H)).subgroupOf
      (generated ![L,R] (Global.sourceS L H)) ≤ normalizer (c₁.actor : Set _))
    (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
    (hm : RootCoordinates.rotationOrder d = 3) (hc : centerIn c₁.actor = ⊥) :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) := by
  obtain ⟨i, _, cmp, _⟩ := D.rankOne_a2_marked_source_recognition
    h hmany hn hpsl hH prep d mark split c₀ c₁ hn₀ hn₁ E₀ E₁ hm hc
  exact A2Source.linear_catalogue_of_flagIso i cmp

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
