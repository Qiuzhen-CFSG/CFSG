module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.Transfer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.LineFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLinearAmbient.LocalCentralizer

/-!
# All-degree involution fusion and central-line incidence for the chosen module

Apply the actual cyclic field-action transfer and root-plane calculations
to the original Chapter12 input. Every ambient involution is fused into S,
there is one ambient involution class, and each original root plane contains
exactly 2^n+1 conjugates of Z(S), partitioning its nonzero vectors.
The original n>1 and both comparison orientations are retained.

Source: Aschbacher–Smith §5.3.6(2), printed p.660, and F.4.46(1), p.297,
applied in Chapter12, p.795 (`refs/quasithin.pdf`). Individual involution
centralizer containment and ambient recognition still require proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric ChapterF.GreenBook.LieModels
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B : Subgroup G} (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
  {n : ℕ} (hn : 1 < n)
  (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (d : Global.Preparation T L H A B (residual H))
  (hp : Group.IsPerfect (residual H))
  (F : Type) [Field F] [Finite F] [CharP F 2]
  {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
  (he : Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F)) ∨
    Nonempty (RankTwoAmalgam.Iso
    (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
    (LinearThree.amalgam F).reverse))
  (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include D h hmany hn hpsl hH d hp hm hF he hmax

omit hmax in
/-- The actual source Sylow index divides the original exponent. -/
theorem rankOne_global_linear_source_sylow_index_dvd :
    (Global.sourceS L H).relIndex (T : Subgroup G) ∣ n :=
  d.linear_source_sylow_index_dvd (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he

omit hmax in
/-- Cyclic field transfer applies to every ambient involution at every degree. -/
theorem rankOne_global_linear_involution_fused_into_sourceS
    (x : G) (hx : orderOf x = 2) :
    ∃ y ∈ Global.sourceS L H, IsConj x y :=
  d.linear_involution_fused_into_sourceS (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he x hx

/-- The original ambient group has one involution class, including even n and q=4. -/
theorem rankOne_global_linear_involutions_isConj
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  d.linear_involutions_isConj (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax x y hx hy

/-- Ambient conjugate central lines in a root plane are already factor-conjugate. -/
theorem rankOne_global_linear_root_line_fusion (i : Fin 2) (g : G)
    (hg : (centerIn (Global.sourceS L H)).conjBy g ≤ (![L,residual H] i).pCoreIn 2) :
    ∃ a ∈ ![L,residual H] i,
      (centerIn (Global.sourceS L H)).conjBy a = (centerIn (Global.sourceS L H)).conjBy g :=
  d.linear_root_line_fusion (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax i g hg

/-- The central lines partition the nonzero original root-plane vectors. -/
theorem rankOne_global_linear_root_line_partition (i : Fin 2) (x : G)
    (hx : x ∈ (![L,residual H] i).pCoreIn 2) (hx1 : x ≠ 1) :
    ∃! U : Subgroup G,
      (∃ a ∈ ![L,residual H] i, (centerIn (Global.sourceS L H)).conjBy a = U) ∧ x ∈ U :=
  d.linear_root_line_partition (D.rankOne_generic_input_of_many h hmany hn hpsl)
    hH hp F hm hF he hmax i x hx hx1

/-- Source §5.3.6(2) with the original Chapter12 exponent and root planes. -/
theorem rankOne_global_linear_root_line_count (i : Fin 2) :
    Nat.card {U : Subgroup G //
      (∃ g : G, (centerIn (Global.sourceS L H)).conjBy g = U) ∧
        U ≤ (![L,residual H] i).pCoreIn 2} = 2^n + 1 := by
  have hi := D.rankOne_generic_input_of_many h hmany hn hpsl
  rw [d.linear_root_line_count hi hH hp F hm hF he hmax i,hF,
    (d.linear_amalgam_blocks hi hH.1.1.2 hp F hm hF he).1]

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
