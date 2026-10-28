module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.Nonfusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.InvolutionTransfer

/-!
# Weak closure and root nonfusion for the original Chapter 12 symplectic pair

With W = wholeReduced T L, the original Sylow has exactly the two pure
parabolic cores as its maximum elementary subgroups. They are weakly closed,
and each original full normalizer controls fusion on its core centralizer.
In particular ambient conjugacy inside Z(S) preserves both root centers.

The Chapter 6 application retains Hypothesis 12.2.1, the many-local condition,
the original PSL₂ quotient, the whole residual and the actual pure comparison
in either orientation. It includes n=2 without assuming S=T or an ambient
order bound. The remaining outer-Sylow and full-centralizer arguments are
still needed for the final order comparison.

Source: Aschbacher–Smith F.4.35, printed p.292, applied through 5.3.3
and Chapter 12, pp.659,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The pure Sylow has exactly the two marked maximum elementary cores,
which generate it and have order q³. -/
theorem rankOne_global_symplectic_inner_max_elementary_pair
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
    Stellmacher.elementaryAbelianMaxSubgroups (Global.sourceS L H) =
      {(ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).pCoreIn 2,
       (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1).pCoreIn 2} ∧
    Stellmacher.elementaryAbelianMaxJ (Global.sourceS L H) = Global.sourceS L H ∧
    ∀ i : Fin 2, Nat.card ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2) =
      Nat.card F^3 :=
  d.symplectic_inner_max_elementary_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- Outer field automorphisms do not create further maximum elementary
subgroups: the full original T has precisely the same two cores as S. -/
theorem rankOne_global_symplectic_max_elementary_sylow_pair
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
    Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
      {(ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 0).pCoreIn 2,
       (ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) 1).pCoreIn 2} ∧
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) = Global.sourceS L H :=
  d.symplectic_max_elementary_sylow_pair
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- Both actual parabolic cores are weakly closed in the ambient Sylow.
The normalizer correction uses the literal whole common normalizer. -/
theorem rankOne_global_symplectic_parabolic_cores_weakly_closed
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
    (i : Fin 2) (g : G)
    (hg : ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    g ∈ normalizer ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2 : Set G) :=
  d.symplectic_parabolic_cores_weakly_closed
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he i g hg

/-- On the centralizer of either actual radical, its full normalizer controls
ambient element fusion. This is stronger than the needed center-only clause. -/
theorem rankOne_global_symplectic_core_centralizer_fusion
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
    (i : Fin 2) {x y : G}
    (hx : x ∈ centralizer ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2 : Set G))
    (hy : y ∈ centralizer ((ChapterF.Source.parabolic ![L,residual H] (Global.sourceS L H) i).pCoreIn 2 : Set G))
    (hxy : IsConj x y) :
    ∃ g ∈ normalizer (![L,residual H] i : Set G), g*x*g⁻¹=y :=
  d.symplectic_core_centralizer_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he i hx hy hxy

/-- Each original full normalizer controls fusion of elements in Z(S),
without the transfer conclusion S=T. -/
theorem rankOne_global_symplectic_center_fusion_control
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
    (i : Fin 2) (x y : Global.sourceS L H)
    (hx : x ∈ center (Global.sourceS L H)) (hy : y ∈ center (Global.sourceS L H))
    (hxy : IsConj x.val y.val) :
    ∃ g ∈ normalizer (![L,residual H] i : Set G), g*x.val*g⁻¹=y.val :=
  d.symplectic_center_fusion_control
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he i x y hx hy hxy

/-- Neither root-center type can fuse to a different type inside Z(S).
This supplies the root nonfusion inside Z(S) used in F.4.37 and F.4.39. -/
theorem rankOne_global_symplectic_root_center_nonfusion
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
    (i : Fin 2) (x y : Global.sourceS L H)
    (hx : x ∈ center (Global.sourceS L H)) (hy : y ∈ center (Global.sourceS L H))
    (hxy : IsConj x.val y.val) :
    x.val ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype ↔
      y.val ∈ (center (![L,residual H] i)).map (![L,residual H] i).subtype :=
  d.symplectic_root_center_nonfusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he i x y hx hy hxy
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
