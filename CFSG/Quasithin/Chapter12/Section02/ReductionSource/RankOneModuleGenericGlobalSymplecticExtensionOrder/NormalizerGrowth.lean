module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.NormalizerGrowth
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterSylow

/-!
# The Chapter 12 outer-centralizer normalizer obstruction

If S<T, the original prepared symplectic pair admits one outer involution
whose centralizer in T is Sylow in both endpoint centralizers. Its larger
ambient two-normalizer escapes both endpoints and cannot preserve an inner
central subgroup meeting either root center. The final application uses the
actual characteristic center-derived subgroup of C_T(f).

These are literal applications with W=wholeReduced T L. They retain
Hypothesis 12.2.1, the many-local assumption, n>1, the PSL₂ quotient,
HStar membership, preparation, perfectness of the whole residual, and both
orientations of the pure comparison, including n=2.

Source: Aschbacher–Smith F.4.37, printed p.293, applied in 5.3.3 and
Chapter 12, pp.659,795 of refs/quasithin.pdf. The native field-fixed
calculation, its q=4 exception, and the final order comparison remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} (D : ChosenModule T L V)
include D

/-- A largest outer centralizer in T is already Sylow in each endpoint centralizer. -/
theorem rankOne_global_symplectic_maximal_outer_centralizer
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
      (∀ g : T, orderOf g=2 → g.val ∉ Global.sourceS L H →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      ∀ i : Fin 2, ∀ U : Subgroup G, IsPGroup 2 U →
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) ≤ U →
        U ≤ centralizer ({f.val} : Set G) →
        U ≤ normalizer (![L,residual H] i : Set G) →
        U = (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) :=
  d.symplectic_maximal_outer_centralizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

/-- Root nonfusion makes the root intersections of every subgroup of Z(S)
invariant under its whole ambient normalizer. -/
theorem rankOne_global_symplectic_center_subgroup_root_intersection_normalized
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
    (E : Subgroup G) (hE : E ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype)
    (i : Fin 2) :
    normalizer (E : Set G) ≤ normalizer
      ((E ⊓ (center (![L,residual H] i)).map (![L,residual H] i).subtype : Subgroup G) : Set G) :=
  d.symplectic_center_subgroup_root_intersection_normalized
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he E hE i

/-- A subgroup of the inner Sylow center meeting a root center has its
whole normalizer in the corresponding original endpoint. -/
theorem rankOne_global_symplectic_center_subgroup_normalizer_le
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
    (E : Subgroup G) (hE : E ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype)
    (i : Fin 2)
    (hne : E ⊓ (center (![L,residual H] i)).map (![L,residual H] i).subtype ≠ ⊥) :
    normalizer (E : Set G) ≤ normalizer (![L,residual H] i : Set G) :=
  d.symplectic_center_subgroup_normalizer_le
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he E hE i hne

/-- In a larger two-normalizer of an outer centralizer, every invariant
subgroup lying in Z(S) avoids both root centers. -/
theorem rankOne_global_symplectic_normalized_center_disjoint_roots
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
    (U : Subgroup G)
    (hout : ∀ i : Fin 2, ¬ U ≤ normalizer (![L,residual H] i : Set G))
    (E : Subgroup G) (hE : E ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype)
    (hnorm : U ≤ normalizer (E : Set G)) (i : Fin 2) :
    Disjoint E ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_normalized_center_disjoint_roots
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he U hout E hE hnorm i

/-- Properness of the inner Sylow produces a larger two-normalizer of a
maximal outer centralizer escaping both original endpoints. -/
theorem rankOne_global_symplectic_outer_centralizer_normalizer_growth
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
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ U : Subgroup G, IsPGroup 2 U ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < U ∧
        U ≤ centralizer ({f.val} : Set G) ∧
        U ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ U ≤ normalizer (![L,residual H] i : Set G)) ∧
        ∀ E : Subgroup G, E ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype →
          U ≤ normalizer (E : Set G) →
          ∀ i : Fin 2, Disjoint E ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_outer_centralizer_normalizer_growth
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

/-- The actual center-derived subgroup in F.4.37 cannot both lie in Z(S)
and meet a root center, for a suitably chosen outer involution. The native
placement and the field-four exception are not assumed or asserted here. -/
theorem rankOne_global_symplectic_outer_derived_center_obstruction
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
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      let C := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
      let Z := (center C ⊓ _root_.commutator C).map C.subtype
      Z ≤ (center (Global.sourceS L H)).map (Global.sourceS L H).subtype →
        ∀ i : Fin 2, Disjoint Z ((center (![L,residual H] i)).map (![L,residual H] i).subtype) :=
  d.symplectic_outer_derived_center_obstruction
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp F hm hF he hst

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
