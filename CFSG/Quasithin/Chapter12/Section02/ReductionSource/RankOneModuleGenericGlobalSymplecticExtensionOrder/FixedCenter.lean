module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.FixedCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.NormalizerGrowth

/-!
# Chapter 12 fixed-center placement for the original symplectic pair

The same outer involution has its fixed inner-Sylow center in Z(S), and
[T,T] lies in S. The characteristic center-derived subgroup of C_T(f)
therefore lies in Z(S). For the involution selected by the ambient
normalizer-growth argument it avoids both original root centers. The
finite two-group center theorem promotes this to the derived subgroup
of the fixed inner Sylow, isolating a purely native remaining calculation.

These literal applications use W=wholeReduced T L and retain Hypothesis
12.2.1, many locals, n>1, the PSL2 quotient, HStar membership, preparation,
the perfect whole residual, and both orientations, including n=2. The
nonbinary fixed-field root intersection and the q=4 exception remain open;
no ambient order bound or completed recognition is asserted.

Source: Aschbacher--Smith F.4.37, printed p.293, applied in 5.3.3 and
Chapter 12, pp.659,795 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- The fixed inner Sylow has no new centralizer inside S: its centralizer
there is the original two-root center. This uses the same outer involution,
without assuming ambient Sylow placement or S=T. -/
theorem rankOne_global_symplectic_inner_fixed_centralizer_le
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    Global.sourceS L H ⊓ centralizer
      ((Global.sourceS L H ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ≤
        (center (Global.sourceS L H)).map (Global.sourceS L H).subtype :=
  d.symplectic_inner_fixed_centralizer_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- The center of the fixed inner Sylow lies in the center of the original S. -/
theorem rankOne_global_symplectic_inner_fixed_center_le
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    let C := Global.sourceS L H ⊓ centralizer ({f.val} : Set G)
    (center C).map C.subtype ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype :=
  d.symplectic_inner_fixed_center_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- The actual Sylow commutator is inner, via the cyclic native outer quotient. -/
theorem rankOne_global_symplectic_sylow_commutator_le_sourceS
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
    (_root_.commutator T).map (T : Subgroup G).subtype ≤ Global.sourceS L H :=
  d.symplectic_sylow_commutator_le_sourceS
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he

/-- The center-derived subgroup in F.4.37 lies in the original inner
Sylow center, for every outer involution in T, including q=4. -/
theorem rankOne_global_symplectic_outer_derived_center_le
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
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ Global.sourceS L H) :
    let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
    (center C ⊓ _root_.commutator C).map C.subtype ≤
      (center (Global.sourceS L H)).map (Global.sourceS L H).subtype :=
  d.symplectic_outer_derived_center_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he f hf ho

/-- Applying the proved placement to the same chosen outer involution
makes its characteristic center-derived subgroup disjoint from both root
centers. Nontrivial root intersection and the field-four exception remain
for the exclusion step. -/
theorem rankOne_global_symplectic_outer_derived_center_disjoint_roots
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
    ∃ f : T, orderOf f=2 ∧ f.val ∉ Global.sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
      let Z := (center C ⊓ _root_.commutator C).map C.subtype
      Z ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype ∧
        ∀ i : Fin 2, Disjoint Z ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_outer_derived_center_disjoint_roots
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

/-- The same maximal outer involution has its fixed inner-Sylow derived
subgroup disjoint from both root centers. This reduces the nonexceptional
contradiction to the native fixed group alone, without classifying the whole
extension centralizer. -/
theorem rankOne_global_symplectic_outer_fixed_derived_disjoint_roots
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
    ∃ f : T, orderOf f=2 ∧ f.val ∉ Global.sourceS L H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let P := Global.sourceS L H ⊓ centralizer ({f.val} : Set G)
      ∀ i : Fin 2, Disjoint ((_root_.commutator P).map P.subtype)
        ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_outer_fixed_derived_disjoint_roots
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
