module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SourceAssembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Source

/-!
# Conditional chosen-natural local geometry

This is the narrow Chapter 11 interface consumed by the Chapter 12
nonbinary-natural assembly.  The flag and Cartan are constructed on the
literal `D.centralQuotientAction`; all residuals and radicals are the ambient
preimages from `LocalGeometry.lean`.  The normalizer and weak-closure source
conditions are applied with their exact source hypotheses.  Inputs which
belong to the independent component, point-fixed, line-action, odd-kernel,
and C.1.32/C.1.34 producers remain explicit.

No model quotient is substituted for the original action, and no conclusion
about closure, component equality, or the final contradiction is asserted.
Source: Aschbacher--Smith 11.0.2--11.2.5, pp.759--770.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source geometry needed by the later nonbinary-natural consumer.

The fields in `normalizer_zero` and `normalizer_central` are the two literal
11.2.3 clauses.  `weak_obstruction` is the source 11.2.5 implication for any
outside subgroup satisfying its displayed plane data; it does not assert the
existence of such a subgroup.
-/
structure SourceGeometry (c : Coordinates D S.field)
    (f : InvariantFlag c) (X : Subgroup G) : Prop where
  flag_unique : f.IsUnique
  flag_inner_unique : f.IsInnerUnique
  local_quotients : ∀ i : Fin 2,
    Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2,S.field.Carrier))
  locals_generate : L = f.Li 0 ⊔ f.Li 1
  cartan : IsCartan T L X
  cartan_normalizes : ∀ i : Fin 3, X ≤ normalizer (f.Vi i : Set G)
  cartan_rank : ∀ p : ℕ, p.Prime → p ∣ 2 ^ S.field.degree - 1 → primeRank p X = 2
  fixed_line : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)
  radical_centralizes_point : f.Vi 0 ≤ centralizer (f.Ri 0 : Set G)
  sylow_normalizer : normalizer (T : Set G) ≤ normalizer (L : Set G)
  normalizer_control : Source.NormalizerControl (f.Vi 2) (f.Vi 0) (f.Li 0)
    (normalizer (L : Set G))
  radical_alternative : Source.RadicalNormalizerAlternative (T : Subgroup G) V
    (f.Vi 0) (f.Ri 0) (normalizer (L : Set G)) L S.field.degree
  normalizer_zero : V ⊓ centralizer (L : Set G) = ⊥ →
    normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
      (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))
  normalizer_central : centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
    normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)
  weak_obstruction : ∀ (H : Subgroup G),
    (T : Subgroup G) ≤ H → ¬ H ≤ normalizer (L : Set G) →
    (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)) →
    (P : Sylow 2 (f.Li 1)) →
    f.Vi 0 = f.Vi 1 ⊓ centralizer
      ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G) →
    f.Ri 1 ≤ centralizer (f.Vi 1 : Set G) →
    (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V, f.Ri 1⁆ ≤ f.Vi 1) →
    Source.WeakClosureObstruction (T : Subgroup G) V (f.Vi 0) H
  odd_kernel : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V)
  maximal_unique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N →
    N = normalizer (L : Set G)
  three_centralizer : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)
  second_component : Source.UniqueNoncentralComponent
    (normalizer (f.Vi 1 : Set G)) (f.Vi 1) (f.Li 1)
  plane_data : ∃ P : Sylow 2 (f.Li 1), f.Vi 0 = f.Vi 1 ⊓ centralizer
    ((P : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G)
  plane_radical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G)
  linear_movement : Nonempty (ActionEquiv D.centralQuotientAction
      (linearNatural S.field 3)) → ⁅V, f.Ri 1⁆ ≤ f.Vi 1

/-- Construct the coherent flag/Cartan and local source outputs from the exact
independent hypotheses.  The odd-kernel premise is retained as an explicit
result for the 11.2.1 consumer; it is not silently reconstructed here.
-/
theorem exists_source_geometry
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
    (hfour : ∀ (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
      (g : InvariantFlag (.sl3 m)), S.field.degree = 2 →
      (¬ normalizer (g.Ri 0 : Set G) ≤ normalizer (L : Set G)) →
      ChapterC.IsSL3EvenBlock L S.field.degree →
      radicalOmegaCenter (g.Ri 0) = g.Vi 0 ⊔ radicalFixedCenter (g.Ri 0) L →
      normalizer (g.Ri 0 : Set G) ≤ normalizer (radicalFixedCenter (g.Ri 0) L : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hodd : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N →
      N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hP : Sylow 2 (f.Li 1))
    (hPfixed : f.Vi 0 = f.Vi 1 ⊓ centralizer
      ((hP : Subgroup (f.Li 1)).map (f.Li 1).subtype : Set G))
    (hradical : f.Ri 1 ≤ centralizer (f.Vi 1 : Set G))
    (hmove : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      ⁅V, f.Ri 1⁆ ≤ f.Vi 1) :
    SourceGeometry D S c f X := by
  have hnorm := Normalizers.chosen_source_normalizers_of_intrinsic_and_linear_four
    D S hlinear hsymplectic f hcomponent hline hres hcubic hfour hX
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
