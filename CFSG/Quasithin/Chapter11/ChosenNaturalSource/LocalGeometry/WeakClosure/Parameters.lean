module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.LowerBound
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Closure
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.RootGeometry.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.Exceptional
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SylowFixed

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalCubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalMaximality

/-!
# Conditional assembly of the four natural-parameter clauses

The consumers prove the residual, minimizing-subspace and conjugate-offender
arguments of 11.2.2(1--4). The exact local parameter is proved by
`localM_eq_naturalParameter`. FixedCodimensions is complete for Sp₄, G₂ and
odd-degree SL₃. In even degree SL₃ retains only the exact earlier cubic
containment of 11.0.4. The A₂ actor calculation is proved for all three
markings in every degree, retaining nonsplit covers, and is applied to the
actual weak closure. Minimal fixed-space recognition is proved for all three markings and applied
to the actual global parameters. Hyperplane centralizers are now controlled
whenever the hyperplane contains C_V(L); in particular all four clauses are
proved for SL₃, where that kernel vanishes. The completed E.6.3 theorem settles every parameter above two, including
all G₂ markings and all higher-degree central extensions. Source uniqueness
over L settles all other kernel orders except two. In the remaining degree-two
Sp₄ case, the original hyperplane is the image of a field complement in the
full orthogonal cover. Its Sylow-fixed intersection, faithful cubic actor and
non-two stabilizer index are proved. Maximality of its stabilizer is the sole
remaining local geometry input. The original
conditional interfaces are preserved below. TI, the three-space
centralizer and the fixed-line identity are preceding 11.0--11.1 results owned by the preliminary, component and
flag producers. No source-theorem completion is asserted until all the
model and lower-bound premises have been discharged.

Source: Aschbacher--Smith, 11.2.2(1--4), printed pp.767--768.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Assembly on the same original seed, action marking and flag throughout.
The three new source obligations remain visible in the signature. -/
theorem source_parameters_of_model_and_lower_bound {c : Coordinates D S.field}
    (f : InvariantFlag c) (hmodel : FixedCodimensions D S c)
    (hroot : RootGeometry D S f)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  have hE := hypothesisE61_of_ti D S hti
  have hparameters := global_parameters D S f hmodel hroot hE hr hthree
  exact ⟨localM_of_fixedCodimensions D S hmodel,
    fun U hUV hk hres => centralizer_control D S hmodel hE hr hUV hk hres,
    hparameters, fun j hj => weakClosure_bound D S f hroot hparameters.2 hline hj⟩


/-- The original hyperplane interface, preserving every public premise. -/
theorem source_parameters_of_model_and_hyperplanes {c : Coordinates D S.field}
    (f : InvariantFlag c) (hmodel : FixedCodimensions D S c)
    (hroot : RootGeometry D S f)
    (hhyper : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  have hE := hypothesisE61_of_ti D S hti
  have hr := lower_bound_of_hyperplanes D S hmodel hE hhyper
  have hparameters := global_parameters D S f hmodel hroot hE hr hthree
  exact ⟨localM_of_fixedCodimensions D S hmodel,
    fun U hUV hk hres => centralizer_control D S hmodel hE hr hUV hk hres,
    hparameters, fun j hj => weakClosure_bound D S f hroot hparameters.2 hline hj⟩

/-- Source clauses (1--4) with every fixed-codimension and root-geometry
calculation discharged. Hyperplane control remains with this parameter task;
the exact earlier cubic, TI, three-space and fixed-line conclusions retain
their preliminary, component and flag owners. The parent
qt-d-1222-natural-weak-closure-source performs final source assembly. -/
theorem source_parameters_of_cubic_and_hyperplanes {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hhyper : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      centralizer (U : Set G) ≤ normalizer (L : Set G))
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  have hmodel := natural_fixedCodimensions_of_cubic_source D S c hcubic
  exact source_parameters_of_model_and_hyperplanes D S f hmodel
    (rootGeometry_of_fixedCodimensions D S f hmodel hti) hhyper hti hthree hline

/-- Source clauses (1--4) when C_V(L)=1, with all owned fixed-space, root
and hyperplane calculations discharged. The exact earlier cubic, TI,
three-space and line conclusions retain their original producers; the parent
qt-d-1222-natural-weak-closure-source discharges them in final assembly. -/
theorem source_parameters_of_central_kernel_eq_bot {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hC : V ⊓ centralizer (L : Set G) = ⊥)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_cubic_and_hyperplanes D S f hcubic
    (fun _U hUV hU => Hyperplanes.centralizer_le_of_central_kernel_eq_bot D S c
      (hypothesisE61_of_ti D S hti) hC hUV hU) hti hthree hline

/-- Source clauses (1--4) outside the order-two central-kernel case.
The uniqueness premise is precisely the earlier 4.2.13 conclusion used on
printed p.767, also retained by the existing normalizer source owner.
No hyperplane-control or numerical conclusion is assumed. -/
theorem source_parameters_of_kernel_card_ne_two {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) ≠ 2)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_cubic_and_hyperplanes D S f hcubic
    (fun _U hUV hU => Hyperplanes.centralizer_le_of_kernel_card_ne_two D S c
      (hypothesisE61_of_ti D S hti) hunique hC hUV hU) hti hthree hline

/-- The complete owned SL₃ branch, in every degree. The central-kernel
premise is discharged by the earlier proved SL₃ cover theorem; only the
permitted earlier-source conclusions remain for the parent assembly. -/
theorem source_parameters_sl3
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S (Coordinates.sl3 m) ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S (Coordinates.sl3 m) →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S (Coordinates.sl3 m) : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S (Coordinates.sl3 m) ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S (Coordinates.sl3 m)) ∧
    (∀ j : ℕ, j < naturalParameter D S (Coordinates.sl3 m) - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_central_kernel_eq_bot D S f hcubic
    (Preliminary.sl3_centralizer_eq_bot D S m) hti hthree hline

/-- All four owned source clauses in the G₂ row, in every nonbinary degree.
Only the earlier TI, three-space and fixed-line conclusions remain explicit,
with final discharge by qt-d-1222-natural-weak-closure-source. -/
theorem source_parameters_g2
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2) (Representation.g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S (Coordinates.g2 m) ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S (Coordinates.g2 m) →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S (Coordinates.g2 m) : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S (Coordinates.g2 m) ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S (Coordinates.g2 m)) ∧
    (∀ j : ℕ, j < naturalParameter D S (Coordinates.g2 m) - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  have hmodel := g2_fixedCodimensions D S m
  have hr := lower_bound_of_parameter_gt_two D S (Coordinates.g2 m)
    (hypothesisE61_of_ti D S hti) (by have hn := S.nonbinary; simp only [naturalParameter]; omega)
  exact source_parameters_of_model_and_lower_bound D S f hmodel
    (rootGeometry_of_fixedCodimensions D S f hmodel hti) hr hti hthree hline

/-- All four owned source clauses in the Sp₄ row above degree two.
Only the earlier TI, three-space and fixed-line conclusions remain explicit,
with final discharge by qt-d-1222-natural-weak-closure-source. -/
theorem source_parameters_sp4_of_degree_gt_two
    (m : ActionEquiv D.centralQuotientAction
      (Representation.restrictScalars (k := ZMod 2) (Representation.symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hn : 2 < S.field.degree)
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S (Coordinates.sp4 m) ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S (Coordinates.sp4 m) →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S (Coordinates.sp4 m) : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S (Coordinates.sp4 m) ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S (Coordinates.sp4 m)) ∧
    (∀ j : ℕ, j < naturalParameter D S (Coordinates.sp4 m) - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  have hmodel := sp4_fixedCodimensions D S m
  have hr := lower_bound_of_parameter_gt_two D S (Coordinates.sp4 m)
    (hypothesisE61_of_ti D S hti) hn
  exact source_parameters_of_model_and_lower_bound D S f hmodel
    (rootGeometry_of_fixedCodimensions D S f hmodel hti) hr hti hthree hline

/-- All four source clauses with only the final orthogonal-stabilizer maximality
calculation left in this task. The cubic actor, Sylow-fixed intersection and
non-two index are discharged on the same original hyperplane. The earlier
cubic-containment, TI, three-space, line and uniqueness inputs retain their
existing producers; their final discharge belongs to
qt-d-1222-natural-weak-closure-source. -/
theorem source_parameters_of_maximal_hyperplane_stabilizers {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hmax : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G))
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  apply source_parameters_of_cubic_and_hyperplanes D S f hcubic _ hti hthree hline
  intro U hUV hU
  by_contra hescape
  exact hescape (Hyperplanes.OriginalCubic.centralizer_le_of_natural_maximal_stabilizer
    D S c (hypothesisE61_of_ti D S hti) hunique hUV hU (hmax U hUV hU hescape))

/-- Source clauses (1--4) after the remaining component-orbit supplement.
The orthogonal stabilizer is now proved maximal in the actual L, through
its nonsplit cover and original quotient. Its supplement in LT, equivalently
the preservation of the L-orbit by T, remains in this task. The earlier
cubic, TI, three-space, fixed-line and uniqueness premises keep their existing
producers and final discharge by qt-d-1222-natural-weak-closure-source. -/
theorem source_parameters_of_stabilizer_supplements {c : Coordinates D S.field}
    (f : InvariantFlag c)
    (hcubic : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    (hsupplement : ∀ U : Subgroup G, U ≤ V → subgroupCorank V U = 1 →
      ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
        localNormalizer (L ⊔ (T : Subgroup G)) U ⊔ L = L ⊔ (T : Subgroup G))
    (hti : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G)) :
    @localM G _ V D.elementary = naturalParameter D S c ∧
    (∀ U : Subgroup G, U ≤ V → subgroupCorank V U < 2 * naturalParameter D S c →
      oddCentralizerCondition (normalizer (L : Set G)) V U →
      centralizer (U : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 2 ↥(centralizer (U : Set G))).map
          (centralizer (U : Set G)).subtype ≤
            normalizer (L : Set G) ⊓ centralizer (V : Set G)) ∧
    (((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c) ∧
    (∀ j : ℕ, j < naturalParameter D S c - 1 →
      indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
        f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G)) := by
  exact source_parameters_of_maximal_hyperplane_stabilizers D S f hcubic hunique
    (fun U hUV hU hescape => Hyperplanes.OriginalMaximality.escaping_hyperplane_maximal_of_supplement
      D S c (hypothesisE61_of_ti D S hti) hunique hUV hU hescape
      (hsupplement U hUV hU hescape)) hti hthree hline

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
