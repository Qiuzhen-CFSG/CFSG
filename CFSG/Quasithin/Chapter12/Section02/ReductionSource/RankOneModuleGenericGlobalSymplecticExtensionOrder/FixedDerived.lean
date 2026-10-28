module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedDerived
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedCenter

/-!
# Chapter 12 nonexceptional symplectic outer-Sylow exclusion

The same fixed-inner-Sylow commutator meets an original root center at
q>4, contradicting the ambient normalizer-growth obstruction. Therefore
S=T for every n>2, and the complete nonroot involution centralizer lies
in the whole common normalizer. The remaining proper-S case has exactly
n=m=2, field order four, and Sylow extension degree two.

These literal applications use W=wholeReduced T L and retain Hypothesis
12.2.1, many locals, the original n>1, the PSL2 quotient, HStar membership,
preparation, the perfect whole residual and both amalgam orientations.
The field-four exception and the full same-extension order comparison
remain necessary for the unconditional source completion.

Source: Aschbacher--Smith F.4.37--39, printed pp.293--294, applied in
5.3.3 and Chapter 12, pp.659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- When q>4, every original outer involution has a fixed inner-Sylow
commutator meeting one of the original root centers nontrivially. The native
long root is matched with the same source endpoint in either orientation. -/
theorem rankOne_global_symplectic_outer_fixed_derived_meets_root
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
    (hm2 : 2<m) (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    let P := Global.sourceS L H ⊓ centralizer ({f.val} : Set G)
    ∃ i : Fin 2, ¬ Disjoint ((_root_.commutator P).map P.subtype)
      ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_outer_fixed_derived_meets_root
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hm2 f hf ho

/-- The nonexceptional symplectic field branch has no even outer part:
the original inner Sylow equals the original ambient Sylow whenever n>2. -/
theorem rankOne_global_symplectic_sourceS_eq_sylow_of_two_lt
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
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) (hn2 : 2<n) :
    Global.sourceS L H=(T : Subgroup G) :=
  d.symplectic_sourceS_eq_sylow_of_two_lt
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hn2

/-- Only the genuine field-four exception can retain a proper inner Sylow.
This does not exclude that final exception. -/
theorem rankOne_global_symplectic_proper_inner_sylow_exponent
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
    (hst : Global.sourceS L H≠(T : Subgroup G)) : n=2 :=
  d.symplectic_proper_inner_sylow_exponent
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

/-- For n>2 the complete ambient centralizer of a nonroot central
involution lies in the whole common normalizer, with S=T now discharged. -/
theorem rankOne_global_symplectic_square_centralizer_le_middle_of_two_lt
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
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)) (hn2 : 2<n)
    (z : Global.sourceS L H) (hz : orderOf z=2) (hsq : ∃ y : Global.sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_two_lt
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hn2 z hz hsq

/-- A proper inner Sylow forces precisely field order four and Sylow
extension degree two. The remaining exceptional argument must retain both. -/
theorem rankOne_global_symplectic_proper_inner_sylow_field_four
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
    (hst : Global.sourceS L H≠(T : Subgroup G)) :
    n=2 ∧ m=2 ∧ Nat.card F=4 ∧ (Global.sourceS L H).relIndex (T : Subgroup G)=2 :=
  d.symplectic_proper_inner_sylow_field_four
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
