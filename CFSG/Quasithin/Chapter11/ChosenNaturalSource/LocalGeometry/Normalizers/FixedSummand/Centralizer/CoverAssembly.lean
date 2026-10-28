module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.ElementaryCover

/-!
# Fixed-center control and source 11.1.5 from the native elementary cover

Apply the shared full-W contradiction to the actual B=L C.2.8 constructor.
This proves uniqueness over L, hence centralizer control for every nonzero
subgroup of the actual radical fixed center. The existing scalar geometry,
11.0.4 theta calculation and TI argument construct the Cartan--TI pair;
the already proved SL3(4) and Sp4(4) block actions exclude order 21. Thus
fixed-center preservation and the original radical alternative now include
degree two with the same literal quotient, radical and invariant flag.

The uniform native cover and embedded linear-five quotient remain explicit,
with producers qt-model-j4-elementary-normalizer-cover and
qt-model-j4-large-center-radicals. Their discharge remains with
qt-d-1222-natural-point-fixed-summand. The preceding fixed-line, 11.0.4,
component and block inputs retain their source producers and final owner
qt-d-1222-natural-normalizer-source. No centralizer, pair, exceptional-action
or source-specific placement callback remains in these conditional results.

Source: Aschbacher--Smith 4.2.13, printed pp.611--612, and 11.1.5,
printed pp.765--766, using the corrected omega-center calculation.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
open Chapter4
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The B=L application preserves the actual full module of the C.2.8 constructor. -/
theorem c28_original_false_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {H M R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M L R W)
    (hstrict : M < H) (hn : M ≤ normalizer (L : Set G)) : False := by
  obtain ⟨_,_,_,K,hK,_⟩ := c28_ordinary_field_four D S h hstrict hn
  have hN := (normal_subgroupOf_iff_le_normalizer h.component_le).mpr hn
  have hc : (L : Set G) = (L : Set G) * (L.pCoreIn 2 : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨x,hx,1,one_mem _,mul_one x⟩
    · rintro x ⟨a,ha,b,hb,rfl⟩
      exact mul_mem ha (pCoreIn_le 2 L hb)
  exact c28_covering_ordinary_false_of_elementary_cover C eC hcover D S h hstrict hN
    le_rfl hc D.le_componentCore (MulEquiv.refl _) (fun _ => rfl) K hK

/-- Uniqueness over the actual L, including field four, from uniform native coverage. -/
theorem unique_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput) :
    UniqueMaximalOvergroup L (normalizer (L : Set G)) := by
  by_contra hu
  obtain ⟨J,H,P,_,_,_,_,_,hstrict,_,hC,_⟩ :=
    Chapter4.Section03.RankOneUniqueness.exists_source_C28 D S.source.toHypothesis1221 hu
  exact c28_original_false_of_elementary_cover C eC hcover D S hC hstrict inf_le_right

/-- Centralizer control for every nonzero subgroup of the original fixed center. -/
theorem fixedCenter_control_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (R U : Subgroup G) (hU : U ≤ radicalFixedCenter R L) (hne : U ≠ ⊥) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) :=
  Pair.fixedCenter_centralizer_control_of_unique
    (unique_of_elementary_cover C eC hcover D S).2.2 U hU hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
open Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual Cartan--TI pair, including degree two, from native coverage and
the preceding fixed-line and 11.0.4 source inputs. -/
theorem pairConstruction_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
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
    PairConstruction D S f := by
  apply Pair.pairConstruction_of_fixed_line_and_source_residuals D S f hline hres hcubic
  intro _ _ _ _ U hU hne
  exact fixedCenter_control_of_elementary_cover C eC hcover D S (f.Ri 0) U hU hne

/-- The original fixed-summand conclusion, including degree two: the center
calculation, TI control and exceptional block actions are discharged. -/
theorem chosen_fixed_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
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
  chosen_fixed_of_pair D S f he hb (PointCohomology.center_eq D S f hb) hn
    (pairConstruction_of_elementary_cover C eC hcover D S f hline hres hcubic)

/-- Actual source 11.1.5 in every nonbinary degree. The native cover and the
preceding flag/Cartan, preliminary, component and block inputs remain explicit. -/
theorem chosen_radicalAlternative_of_elementary_cover
    (C : Subgroup Janko4.Model) (eC : (C ⧸ pCore 2 C) ≃* PSL(5,ZMod 2))
    (hcover : JankoElementaryNormalizerCover C)
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
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_fixed_line_residuals_and_control D S f hn
    (fun he => PointBlocks.point_blocks_with_span D (hblocks he))
    (fun _ hb => PointCohomology.center_eq D S f hb) hline hres hcubic
  intro _ _ _ _ U hU hne
  exact fixedCenter_control_of_elementary_cover C eC hcover D S (f.Ri 0) U hU hne

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
