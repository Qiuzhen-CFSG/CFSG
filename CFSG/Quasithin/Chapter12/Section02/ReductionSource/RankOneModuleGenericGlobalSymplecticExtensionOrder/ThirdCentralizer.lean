module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.ThirdCentralizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder

/-!
# The original Chapter 12 third-centralizer application

For W = wholeReduced T L, the chosen module gives the two actual parabolic
cores and all noncentral involution centralizers of the inner Sylow.
Conditional on the earlier transfer equality S = T, its center normalizer
is exactly the full middle, and each square involution has its whole
ambient centralizer in that middle. These are global containments,
including every element outside the pure parabolics.

The original Hypothesis 12.2.1, many-local assumption, PSL₂ quotient,
whole residual and compatible pure comparison are retained. Both
orientations and n = 2 are included. The transfer equality remains to
be discharged before assembling the order comparison.

Source: Aschbacher–Smith F.4.39, printed p.294, applied to the prepared
pair of 5.3.1–3, pp.658–659 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal parabolic cores give the inner Sylow wing geometry. -/
theorem rankOne_global_symplectic_sylow_wing_geometry
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) :
    IsElementaryAbelian 2 (center (Global.sourceS L H)) ∧
      (∀ i : Fin 2, IsElementaryAbelian 2
        ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2)) ∧
      (∀ x : Global.sourceS L H, x^2=1 → x ∉ center (Global.sourceS L H) →
        ∃ i : Fin 2, (centralizer ({x} : Set (Global.sourceS L H))).map
          (Global.sourceS L H).subtype =
          (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2) :=
  d.symplectic_sylow_wing_geometry
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- After S = T, the center normalizer is the entire full middle. -/
theorem rankOne_global_symplectic_center_normalizer_eq_middle_of_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hST : Global.sourceS L H = (T : Subgroup G)) :
    normalizer ((center (Global.sourceS L H)).map (Global.sourceS L H).subtype : Set G) =
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_center_normalizer_eq_middle_of_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hST

/-- Conditional on transfer, the full ambient third-involution centralizer
is contained in the original whole normalizer intersection. -/
theorem rankOne_global_symplectic_square_centralizer_le_middle_of_sylow
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A B : Subgroup G} (d : Global.Preparation T L H A B (residual H))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (Global.sourceParabolicAmalgam ![L,residual H] (Global.sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (hST : Global.sourceS L H = (T : Subgroup G))
    (z : Global.sourceS L H) (hz : orderOf z = 2)
    (hsq : ∃ y : Global.sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hST z hz hsq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
