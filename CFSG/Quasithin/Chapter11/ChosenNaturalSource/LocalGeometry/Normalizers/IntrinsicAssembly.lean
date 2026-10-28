module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SourceAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.NativeSource

/-!
# Normalizer restrictions from the intrinsic classifications

The local point exclusions select the actual SL₃ or Sp₄ block in LR₁,
using the Sylow subgroup T ∩ LR₁. The corrected cohomology calculation and
the completed native fixed-summand argument give the exact radical
alternative, including SL₃(4). Feeding it into the marked line-action
argument gives both clauses of 11.2.3 on the same flag and Cartan.

The only classification premises are the precise intrinsic outputs owned
by qt-c134-nonbinary-linear-three-source and qt-c132-nonbinary-symplectic.
The preceding component, fixed-line and 11.0.4 premises, and final discharge
of these intrinsic inputs, belong to qt-d-1222-natural-local-geometry.
In particular no field-four fixed-center or native-cover premise remains.
This is the conditional normalizer family, not an unconditional assertion
of the earlier source theorems.

Source: Aschbacher--Smith 11.1.4--5 and 11.2.3, pp.765--766,768--769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
open ChapterC.RankTwo.NonbinarySymplectic
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The ordinary centralizer consequence of 11.1.4, on the same literal flag. -/
theorem chosen_source_three_centralizer_of_component
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1)) :
    centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G) := by
  have hn := chosen_source_11_1_4_of_component D S f hunique
  intro g hg
  apply hn.1 g
  refine ⟨Subgroup.centralizer_le_normalizer _ hg,
    Subgroup.centralizer_le_normalizer _ (centralizer_le (f.Vi_mono (by decide : (0 : Fin 3) ≤ 2)) hg), ?_⟩
  intro x hx
  rw [← hg x hx, mul_inv_cancel_right, mul_inv_cancel]
  exact (f.Vi 0).one_mem

variable
  (hlinear : ∀ R U : Subgroup G,
    LinearThreeMSPair KnownSimple.IsKnownSimple L R S.field.degree S.field.Carrier →
    Chapter1.IsSylowIn 2 U (L ⊔ R) → R ≤ U →
    ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier),
      PointBlocks.Linear.PointModuleCases D S R U e)
  (hsymplectic : ∀ R : Subgroup G,
    Input (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R)) S.field.degree S.field.Carrier →
      ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R)))

include hlinear hsymplectic

/-- Both 11.1.4 containments, the full 11.1.5 alternative and both 11.2.3
clauses. The fixed-summand input is discharged in every nonbinary degree. -/
theorem chosen_source_normalizers_of_intrinsic
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (hunique : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    {X : Subgroup G} (hX : IsCartan T L X) :
    Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
      (normalizer (L : Set G)) ∧
    Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree ∧
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  have hr := FixedSummand.chosen_source_11_1_5_of_intrinsic D S hlinear hsymplectic f
    hunique hline hres hcubic
  exact ⟨chosen_source_11_1_4_of_component D S f hunique, hr,
    chosen_source_11_2_3_of_intrinsic_sp4_classification D S f hX
      (hsymplectic (T : Subgroup G)) hr⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The actual local-geometry consumer with its normalizer fields proved.
The component and 11.0.4 inputs and the independent weak-closure data remain
explicit for qt-d-1222-natural-local-geometry. Fixed-center preservation,
Sylow-normalizer control, uniqueness over L and the third-space centralizer
are supplied by their proofs, including at field four. -/
theorem sourceGeometry_of_intrinsic
    {c : Coordinates D S.field}
    (hlinear : ∀ R U : Subgroup G,
      CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.LinearThreeMSPair
        KnownSimple.IsKnownSimple L R S.field.degree S.field.Carrier →
      Chapter1.IsSylowIn 2 U (L ⊔ R) → R ≤ U →
      ∃ e : (L ⧸ pCore 2 L) ≃* SL(3,S.field.Carrier),
        Normalizers.PointBlocks.Linear.PointModuleCases D S R U e)
    (hsymplectic : ∀ R : Subgroup G,
      ChapterC.RankTwo.NonbinarySymplectic.Input
        (L.subgroupOf (L ⊔ R)) (R.subgroupOf (L ⊔ R))
        S.field.degree S.field.Carrier →
      ChapterC.IsSp4FourBlock (L.subgroupOf (L ⊔ R)))
    {f : InvariantFlag c}
    (hf : f.IsUnique ∧ f.IsInnerUnique ∧
      (∀ i : Fin 2, Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))) ∧
      L = f.Li 0 ⊔ f.Li 1)
    (hcomponent : Source.UniqueNoncentralComponent (normalizer (f.Vi 1 : Set G))
      (f.Vi 1) (f.Li 1))
    {X : Subgroup G} (hX : IsCartan T L X)
    (hcartan_normalizes : ∀ i : Fin 3, X ≤ normalizer (f.Vi i : Set G))
    (hcartan_rank : ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → primeRank p X = 2)
    (hline : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G))
    (hcent : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G))
    (hres : ∀ p : ℕ, p.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          p ∣ 2 ^ S.field.degree - 1 ∧ 3 < p) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          p ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual p (normalizer (L : Set G)) = L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hodd : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hP : Sylow 2 (f.Li 1))
    (hPfixed : f.Vi 0 = f.Vi 1 ⊓ centralizer
      ((hP : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hmove : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V, f.Ri 1⁆ ≤ f.Vi 1) :
    SourceGeometry D S c f X := by
  have hnorm := Normalizers.chosen_source_normalizers_of_intrinsic
    D S hlinear hsymplectic f hcomponent hline hres hcubic hX
  have hNT := Normalizers.sylow_normalizer_le_of_intrinsic_sp4_classification
    D S c (hsymplectic (T : Subgroup G))
  have hunique := (Normalizers.FixedSummand.Centralizer.chosen_uniqueMaximalOvergroup D S).2.2
  have hthree := Normalizers.chosen_source_three_centralizer_of_component D S f hcomponent
  refine {
    flag_unique := hf.1
    flag_inner_unique := hf.2.1
    local_quotients := hf.2.2.1
    locals_generate := hf.2.2.2
    cartan := hX
    cartan_normalizes := hcartan_normalizes
    cartan_rank := hcartan_rank
    fixed_line := hline
    radical_centralizes_point := hcent
    sylow_normalizer := hNT
    normalizer_control := hnorm.1
    radical_alternative := hnorm.2.1
    normalizer_zero := hnorm.2.2.1
    normalizer_central := hnorm.2.2.2
    weak_obstruction := ?_
    odd_kernel := hodd
    maximal_unique := hunique
    three_centralizer := hthree
    second_component := hcomponent
    plane_data := ⟨hP, hPfixed⟩
    plane_radical := hradical
    linear_movement := hmove }
  intro H hTH hout hSL P hfixP hrad hmv
  exact WeakClosure.source_weakClosureObstruction D S f hunique hthree hline.le
    hcomponent H hTH hout hSL P hfixP hrad hmv

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
