module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.InvolutionTransfer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.ThirdCentralizer

/-!
# Involution transfer in the original Chapter 12 symplectic pair

For W = wholeReduced T L, every ambient involution is conjugate into the
actual Z(S), with the local conjugators transported through the original
pure comparison. The full centralizer has characteristic two and Sylow
two-subgroup order at least q⁴. The exact original index [T:S] divides n.
At odd degree S=T and the full third centralizer lies in the whole middle.

The original Hypothesis 12.2.1, many-local assumption, PSL₂ quotient and
whole residual are retained, in both orientations and including n=2.
Even-degree outer Sylow placement and the full-extension order comparison
remain required for the unconditional GlobalExit.

Source: Aschbacher–Smith F.4.30 and F.4.38–39, printed pp.290,294,
applied in 5.3.3 and Chapter 12, pp.659,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The literal inner Sylow has order q⁴ and parabolic fusion into its center. -/
theorem rankOne_global_symplectic_inner_sylow_card_and_fusion
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
    Nat.card (Global.sourceS L H) = Nat.card F^4 ∧
    ∀ x : Global.sourceS L H, x^2=1 → ∃ g ∈ L ⊔ residual H,
      ∃ z : Global.sourceS L H, z ∈ center (Global.sourceS L H) ∧ g*x.val*g⁻¹=z.val :=
  d.symplectic_inner_sylow_card_and_fusion
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The full original Sylow index divides the original field degree. -/
theorem rankOne_global_symplectic_source_sylow_index_dvd
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
    (Global.sourceS L H).relIndex (T : Subgroup G) ∣ n :=
  d.symplectic_source_sylow_index_dvd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- Cyclic transfer places every ambient involution in the original S. -/
theorem rankOne_global_symplectic_involution_fused_into_sourceS
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
    (x : G) (hx : orderOf x=2) :
    ∃ y ∈ Global.sourceS L H, IsConj x y :=
  d.symplectic_involution_fused_into_sourceS
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he x hx

/-- Every ambient involution is conjugate into the actual Z(S). -/
theorem rankOne_global_symplectic_involution_fused_into_center
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
    (x : G) (hx : orderOf x=2) :
    ∃ z : Global.sourceS L H, z ∈ center (Global.sourceS L H) ∧ IsConj x z.val :=
  d.symplectic_involution_fused_into_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he x hx

/-- Every full ambient involution centralizer has characteristic two. -/
theorem rankOne_global_symplectic_involution_centralizer_characteristicTwo
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
    (x : G) (hx : orderOf x=2) :
    HasCharacteristicTwo (centralizer ({x} : Set G)) ∧
      generalizedFitting (centralizer ({x} : Set G)) = pCore 2 (centralizer ({x} : Set G)) :=
  d.symplectic_involution_centralizer_characteristicTwo
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he x hx

/-- Every ambient involution centralizer has Sylow two-order at least q⁴. -/
theorem rankOne_global_symplectic_involution_centralizer_sylow_lower_bound
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
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    Nat.card F^4 ≤ Nat.card P :=
  d.symplectic_involution_centralizer_sylow_lower_bound
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he x hx P

/-- At odd original degree the inner and ambient Sylows agree. -/
theorem rankOne_global_symplectic_sourceS_eq_sylow_of_odd
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
    (hnodd : Odd n) :
    Global.sourceS L H = (T : Subgroup G) :=
  d.symplectic_sourceS_eq_sylow_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnodd

/-- At odd degree the full third centralizer lies in the whole middle. -/
theorem rankOne_global_symplectic_square_centralizer_le_middle_of_odd
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
    (hnodd : Odd n) (z : Global.sourceS L H) (hz : orderOf z=2)
    (hsq : ∃ y : Global.sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_odd
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hnodd z hz hsq

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
