module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Sp4
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3.Complete
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Pair.Geometry.Construction

/-!
# Complete exceptional exclusion on the original point radical

The SL₃ branch uses the actual two natural sections and the seven-residual.
The Sp₄ branch identifies V₃ with [[R₁,R₁],L₁], so preservation of L₁
also preserves V₃. In both rows the original normalizer bounds contradict
escape. The incompatible G₂ marking is excluded by the proved model-order
comparison. Thus every clause of `ExceptionalBlockActions` is discharged.

The final application assembles scalar geometry, theta and this exceptional
exclusion into the literal radical alternative. Fixed-center centralizer
control remains explicit and remains owned by
qt-d-1222-natural-point-fixed-summand; it is not claimed here as a source
hypothesis or a completed theorem. The preceding fixed-line, 11.0.4, block,
center and 11.1.4 inputs are discharged by the existing source producers
and their final owner qt-d-1222-natural-normalizer-source.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed pp.765–766.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The complete literal exceptional block-action contract. -/
theorem exceptionalBlockActions
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) :
    ExceptionalBlockActions D S f := by
  intro _ _ hb hc X _ _ hp hf he
  have hs : ChapterC.IsShort L := hb.elim (fun h => h.2.1) (fun h => h.1)
  cases c with
  | sl3 m => exact Or.inl (SL3.exceptional_normalizes_seed D S m f hs X hc hp hf he)
  | sp4 m => exact Or.inr (Sp4.exceptional_normalizes_third_and_first D S m f hs X hc hf he)
  | g2 m => exact (PointCohomology.PointGeometry.no_g2_block_marking D S m hb).elim

/-- The original fixed-summand target with the entire exceptional calculation
discharged. The Cartan–TI construction is the only local obligation here. -/
theorem chosen_fixed_of_pair
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (he : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hc : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hp : PairConstruction D S f) :
    normalizer (f.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (f.Ri 0) L : Set G) := by
  have hspan := (PointBlocks.point_blocks_with_span D hb).1
  exact chosen_fixed_of_pair_and_block_action D S f he hn
    (hp he hspan hb hc) (exceptionalBlockActions D S f he hspan hb hc)

/-- The complete symplectic radical alternative, conditional only on the
permitted preceding block, center and source 11.1.4 inputs. The direct
commutator argument discharges fixed-summand invariance in every case. -/
theorem Sp4.radicalAlternative
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hb : ChapterC.IsSp4FourBlock L)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hc : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree := by
  apply chosen_radicalAlternative_of_source_steps D S f
    (fun _ => ⟨PointBlocks.seed_eq_conjugateSpan_of_short D hb.1,Or.inr hb⟩)
    (fun he _ => hc he)
  intro he _ hz
  exact Sp4.normalizes_fixed D S m f hb.1 he hz hn

/-- Application to the literal radical alternative. All local exceptional
and scalar calculations are proved; source TI centralizer control is the
remaining obligation of the fixed-summand owner. -/
theorem chosen_radicalAlternative_of_fixed_line_residuals_and_control
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hn : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0) (normalizer (L : Set G)))
    (hblocks : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V ∧
        (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L))
    (hcenter : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hcontrol : (¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      V = Source.conjugateSpan (normalizer (L : Set G)) V →
      (ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L) →
      radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L →
      ∀ U : Subgroup G, U ≤ radicalFixedCenter (f.Ri 0) L → U ≠ ⊥ →
      centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree :=
  chosen_radicalAlternative_of_constructions D S f hn hblocks hcenter
    (Pair.pairConstruction_of_fixed_line_and_source_residuals D S f hline hres hcubic hcontrol)
    (exceptionalBlockActions D S f)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
