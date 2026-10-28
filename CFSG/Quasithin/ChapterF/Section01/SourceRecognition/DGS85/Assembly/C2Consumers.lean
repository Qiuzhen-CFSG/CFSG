module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.C2Source
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Catalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.SymplecticNativeApplication
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalCatalogue

/-!
# The original C₂ consumer from the reduced natural profile

The b=1 natural actors belong to the original reduced family. Idempotence
transports them to the literal reduced pair before applying equal-linear
recognition. The resulting full reduced comparison feeds Chapter 15 native
restoration. The selected nonsolvable endpoints exclude field two, and the
original quotient markings identify the defining degree with the input n.
Both original endpoint squares, the full original Borel, both natural blocks,
the original right core and containment of the same source S are retained.

The natural profile, marked split quotient and rotation order four are earlier
source premises. Exhaustive row selection and their construction remain with
source assembly. The GlobalExit application additionally uses the existing
preparation with selected factor equal to the whole residual.

Source: DGS (1985), (10.5), Theorem D and (15.2), pp.156,224,226--228;
Aschbacher--Smith F.1.12, 5.2.6 and 12.2.2, pp.263--264,650--651,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.C2Source
open FongSeitzBinary OriginalExtension
variable {G X k₁ W₀ W₁ : Type*} {k₀ : Type} [Group G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {L R S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The full reduced catalogue row, with its positive field degree derived
from the actual field and its native orientation retained. -/
theorem reduced_alternative (h : HypothesisF11 ![L,R] S)
    (p : Profile ![L,R] S k₀ k₁ W₀ W₁)
    (Q : MarkedQuotient P) (e : Iso (reducedAmalgam ![L,R] S) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives L R S := by
  obtain ⟨point,he⟩ := reduced_comparison h p Q e split hm
  let := Fintype.ofFinite k₀
  obtain ⟨m,_,hF⟩ := FiniteField.card k₀ 2
  exact .symplectic k₀ m m.property (by simpa only [Nat.card_eq_fintype_card] using hF) point he

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.C2Source

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.Assembly.C2Source ChapterF.Source.DGS85.OriginalExtension
variable {G X k₁ W₀ W₁ : Type*} {k₀ : Type} [Group G] [Finite G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  {P : Fin 2 → Subgroup X}

/-- Restore the actual source row on every prepared perfect R. The original
markings derive the field equality and both natural blocks; the original
normalized Borel derives the right-core identity and source-S containment. -/
theorem comparison_and_core_of_reduced_bOne_quadrangle
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (p : Profile ![L,R] (sourceS L H) k₀ k₁ W₀ W₁)
    (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L,R] (sourceS L H)) Q.standardAmalgam)
    (split : SplitData Q.tits) (hm : rotationOrder Q = 4) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) ∧
      Nat.card k₀ = 2^n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ sourceS L H ≤ R := by
  obtain ⟨point,⟨f⟩⟩ := reduced_comparison (d.hypothesisF11 h hTH) p Q e split hm
  let := Fintype.ofFinite k₀
  obtain ⟨m,_,hF⟩ := FiniteField.card k₀ 2
  have hcard : Nat.card k₀ = 2^(m : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hF
  obtain ⟨hc,he,hn,hL,hR⟩ := symplectic_original_comparison_of_reduced_iso
    d h hTH hp k₀ m.property hcard point f
  have hcore := symplectic_original_core_and_containment_of_reduced_iso
    d h hTH hp k₀ m.property hcard point f
  refine ⟨?_, hcard.trans (congrArg (fun z => 2^z) he), hL, hR, hcore⟩
  apply ConcreteAmalgamComparison.symplectic k₀ m m.property hcard
  cases point
  · exact Or.inr hc
  · exact Or.inl hc

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.FongSeitzBinary
open ChapterF.Source.DGS85.Assembly.C2Source ChapterF.Source.DGS85.OriginalExtension
variable {G X k₁ W₀ W₁ : Type*} {k₀ : Type} [Group G] [Finite G] [Group X]
  [Field k₀] [Finite k₀] [CharP k₀ 2] [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  {A B R : Subgroup G} (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
  (p : Profile ![L,R] (Global.sourceS L H) k₀ k₁ W₀ W₁)
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam ![L,R] (Global.sourceS L H)) Q.standardAmalgam)
  (split : SplitData Q.tits) (hm : rotationOrder Q = 4)

include D h hmany hn hpsl hH d hp p e split hm in
/-- Apply the selected C₂ source construction to the literal Chapter 12 pair,
retaining the original KnownSimple/proper-K hypotheses and same selected R. -/
theorem rankOne_comparison_and_core_of_reduced_bOne_quadrangle :
    Global.ConcreteAmalgamComparison
      (Global.sourceParabolicAmalgam ![L,R] (Global.sourceS L H)) ∧
      Nat.card k₀ = 2^n ∧ ChapterC.IsL2EvenBlock L n ∧ ChapterC.IsL2EvenBlock R n ∧
      (R ⊔ Global.sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧ Global.sourceS L H ≤ R :=
  d.comparison_and_core_of_reduced_bOne_quadrangle
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp p Q e split hm

omit d hp p e in
include D h hmany hn hpsl hH split hm in
/-- The constructed original comparison feeds the existing strict GlobalExit
when the selected factor is the whole residual. No original comparison is assumed. -/
theorem rankOne_globalExit_of_reduced_bOne_quadrangle
    (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (p : Profile ![L,residual H] (Global.sourceS L H) k₀ k₁ W₀ W₁)
    (e : Iso (reducedAmalgam ![L,residual H] (Global.sourceS L H)) Q.standardAmalgam) :
    RankOneModule.GlobalExit G :=
  D.rankOne_globalExit_of_prepared_comparison h hmany hn hpsl hH d hp
    (D.rankOne_comparison_and_core_of_reduced_bOne_quadrangle
      h hmany hn hpsl hH d hp p Q e split hm).1

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
