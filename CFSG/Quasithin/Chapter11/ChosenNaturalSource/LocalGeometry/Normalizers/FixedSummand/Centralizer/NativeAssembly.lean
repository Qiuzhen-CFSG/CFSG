module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.CoverAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.NativeCover

/-!
# Fixed-center control and the point-radical conclusion

The native full-normalizer cover and embedded linear-five quotient discharge
all model inputs of CoverAssembly. The B=L application gives uniqueness over
L and centralizer control for the actual fixed center. The established scalar
marking, theta identity, TI orbit and exceptional block-action arguments then
prove fixed-center preservation and the original radical alternative, in every
nonbinary degree.

Only the genuine preceding fixed-line, 11.0.4, component and block inputs remain.
Their final source assembly belongs to qt-d-1222-natural-normalizer-source.
There are no coverage, placement, centralizer, Cartan--TI or exceptional-action
callbacks. The original quotient, radical and flag are unchanged.
Source: Aschbacher--Smith 4.2.13, pp.611--612, and 11.1.5, pp.765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open Janko4.LocalStructure.LinearFive (M_F M_F_intrinsicQuotient)
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual B=L constructor is impossible, retaining its full W. -/
theorem c28_original_false
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) : False :=
  c28_original_false_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S h hstrict hn

/-- Uniqueness over L, including the degree-two SL3(4) case. -/
theorem chosen_uniqueMaximalOvergroup
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    UniqueMaximalOvergroup L (normalizer (L : Set G)) :=
  unique_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S

/-- Every nonzero subgroup of the original fixed center has its centralizer in N(L). -/
theorem fixedCenter_centralizer_control
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (R U : Subgroup G) (hU : U ≤ radicalFixedCenter R L) (hne : U ≠ ⊥) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  fixedCenter_control_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S R U hU hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
open Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal Cartan--TI pair from the fixed-line and original 11.0.4 identities. -/
theorem pairConstruction
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    PairConstruction D S f :=
  pairConstruction_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S f hline hres hcubic

/-- The normalizer of the original point radical preserves its actual fixed center. -/
theorem chosen_fixed
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) :=
  chosen_fixed_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S f he hb hn hline hres hcubic

/-- The original 11.1.5 radical alternative, including degree two, from the preceding source inputs. -/
theorem chosen_radicalAlternative
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  chosen_radicalAlternative_of_elementary_cover M_F
    (M_F_intrinsicQuotient.trans Representation.SL5TenDimensional.projectiveEquiv)
    native_janko_elementaryNormalizerCover D S f hn hblocks hline hres hcubic

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
