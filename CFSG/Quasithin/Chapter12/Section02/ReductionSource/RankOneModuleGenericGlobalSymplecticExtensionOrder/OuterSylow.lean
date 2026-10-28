module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.InvolutionTransfer

/-!
# Outer-centralizer bounds for the original Chapter 12 symplectic pair

For W=wholeReduced T L the original Sylow acts faithfully on the native
symplectic group, with inner preimage S. An outer involution has centralizer
in T of order strictly below q⁴. Properness S<T constructs such an involution
and a strictly larger ambient centralizer Sylow, giving the contrary
configuration needed in F.4.37.

The original Hypothesis 12.2.1, many-local assumption, n>1, PSL₂ quotient,
HStar membership, preparation, whole residual and compatible comparison are
retained, in both orientations and including n=2. Ambient Sylow placement,
S=T and the unconditional extension order comparison remain open.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294, and the applications
in 5.3.3 and Chapter 12, pp.659,795 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The original Sylow acts faithfully on the native group, with exactly S as its inner preimage. -/
theorem rankOne_global_symplectic_sylow_native_action
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
    ∃ ρ : T →* MulAut (Sp F), Function.Injective ρ ∧
      (∀ g, DiagramAutomorphisms.PreservesDiagram (ρ g)) ∧
      ∀ g, ρ g ∈ MulAut.innerSubgroup (Sp F) ↔ g.val ∈ Global.sourceS L H :=
  d.symplectic_sylow_native_action
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The centralizer in S of an outer involution has order at most q². -/
theorem rankOne_global_symplectic_outer_inner_centralizer_bound
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
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    Nat.card (Global.sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) ≤ Nat.card F^2 :=
  d.symplectic_outer_inner_centralizer_bound
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

/-- The entire centralizer in T retains the actual outer index [T:S]. -/
theorem rankOne_global_symplectic_outer_sylow_centralizer_bound
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
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) ≤
      Nat.card F^2 * (Global.sourceS L H).relIndex (T : Subgroup G) :=
  d.symplectic_outer_sylow_centralizer_bound
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

/-- The outer-involution centralizer in T is strictly smaller than the inner Sylow. -/
theorem rankOne_global_symplectic_outer_sylow_centralizer_lt
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
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    Nat.card ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) < Nat.card F^4 :=
  d.symplectic_outer_sylow_centralizer_lt
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

/-- The full ambient centralizer has larger Sylow order than C_T(f). -/
theorem rankOne_global_symplectic_outer_centralizer_not_sylow
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
    (f : T) (hf : orderOf f=2) (hfo : f.val ∉ Global.sourceS L H) :
    ¬ Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
      (centralizer ({f.val} : Set G)) :=
  d.symplectic_outer_centralizer_not_sylow
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf hfo

/-- Properness of S constructs an actual outer involution in T, with no splitting premise. -/
theorem rankOne_global_symplectic_outer_involution_exists
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
    (hst : Global.sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ Global.sourceS L H :=
  d.symplectic_outer_involution_exists
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

/-- Properness of S produces the actual centralizer-growth configuration. -/
theorem rankOne_global_symplectic_outer_involution_centralizer_growth
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
    (hst : Global.sourceS L H ≠ (T : Subgroup G)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ Global.sourceS L H ∧
      ∃ R : Sylow 2 (centralizer ({f.val} : Set G)),
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) <
          (R : Subgroup (centralizer ({f.val} : Set G))).map
            (centralizer ({f.val} : Set G)).subtype :=
  d.symplectic_outer_involution_centralizer_growth
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
