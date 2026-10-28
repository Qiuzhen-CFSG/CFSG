module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitRows
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.CoverRecovery
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.FixedGeometry
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Setup
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original quotient and coordinates in the doubled binary row

The action-image marking from DoubledOrbitRows turns the original surjection
L/O₂(L) → Aut_L(W) into a perfect central cover of binary SL₄ or SL₅. The
existing cover theorems and O₂(L/O₂(L)) = 1 make this literal projection
injective. No Irr⁺ premise is imposed on the reducible orbit.

The same group marking transports the B.5.1 natural-plus-dual coordinates to
the original subgroup W = componentOrbit V T. The final formula is literal
ambient conjugation, with the original two-core quotient map. The full
normalizer quotient is a separate remaining obligation of this task, used
by DoubledOrbitApplications. The implementation import exposes only the
original quotient construction for its evaluation on representatives.

Source: Aschbacher--Smith, B.5.1(3), I.1.1--4 and 12.2.2,
printed pp.99,407--408,795. The binary cover mathematics is reused from
ModuleClassification/CoverRecovery and its PSL4Two/PSL5Two inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit
open PerfectCentralCovering

/-- The already proved binary cover calculations kill the kernel of an
actual perfect central cover with trivial two-core. -/
private theorem binary_cover_injective
    {P : Type*} [Group P] [Finite P] [IsQuasisimple P] (hcore : pCore 2 P = ⊥)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (c : PerfectCentralCovering.Cover P (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))) :
    Function.Injective c.toMonoidHom := by
  rcases hn with rfl | rfl
  · let e := Atlas.Order20160A8.sl4TwoEquivPSL
    let f : PerfectCentralCovering.Cover P
        (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) :=
      ⟨e.toMonoidHom.comp c.toMonoidHom,e.surjective.comp c.surjective,c.isPerfect,by
        intro x hx
        exact c.ker_le_center (e.injective (hx.trans e.map_one.symm))⟩
    let S := Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)
    let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple S := IsQuasisimple.of_mulEquiv
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.symm
    let U := universalQuasisimpleCover S
    let m := Matrix.PSL4Two.kernelEquivTwo (ZMod 2) (by simp) (MulEquiv.refl S) U
      (universalQuasisimpleCover_isUniversal S)
    have hm : IsPGroup 2 U.toMonoidHom.ker := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_congr m.toEquiv]; simp)
    have hf := (universalQuasisimpleCover_isUniversal S).injective_of_pGroup_kernel
      hm f.toCovering hcore
    intro a b hab
    exact hf (congrArg e hab)
  · let e := Theory.SpecificGroups.PSL5Two.UniversalCover.projectiveEquivSL.symm
    let f : PerfectCentralCovering.Cover P
        (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
      ⟨e.toMonoidHom.comp c.toMonoidHom,e.surjective.comp c.surjective,c.isPerfect,by
        intro x hx
        exact c.ker_le_center (e.injective (hx.trans e.map_one.symm))⟩
    have hf := f.injective_of_universalProjection_ker_eq_bot
      Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot
    intro a b hab
    exact hf (congrArg e hab)
open CFSG.Quasithin.ChapterB.QuasisimpleSource BinaryLinear.OuterCyclic BinaryNaturalDual

private theorem naturalDual_linear_intertwines
    {P X : Type*} [Group P] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) P X) {n : ℕ}
    (a : ActionEquiv σ (naturalPlusDual n)) (g : P) (x : X) :
    naturalDualRepresentation (slEquivLinear n (a.groupEquiv g)) (a.linearEquiv x) =
      a.linearEquiv (σ g x) :=
  (NaturalDualCentralizer.action_apply n (a.groupEquiv g) (a.linearEquiv x)).symm.trans
    (a.intertwines g x).symm

end CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbit

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource BinaryLinear.OuterCyclic BinaryNaturalDual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- Recover the literal quotient projection from a binary marking of the
whole orbit component. No irreducibility of the doubled orbit is used. -/
theorem doubledOrbit_projection_injective
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : D.orbitComponent ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :
    Function.Injective (D.orbitComponentQuotientHom h) := by
  let := h.quasisimple
  let q := D.orbitComponentQuotientHom h
  have hq := D.orbitComponentQuotientHom_surjective h
  let c : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    ⟨e.toMonoidHom.comp q,e.surjective.comp hq,inferInstance,by
      intro x hx
      rw [← IsQuasisimple.comap_center_of_surjective q hq]
      change q x ∈ center D.orbitComponent
      have hx' : q x = 1 := e.injective (hx.trans e.map_one.symm)
      rw [hx']
      exact one_mem _⟩
  have hi := ModuleClassification.DoubledOrbit.binary_cover_injective
    (pCore_quotient_pCore_eq_bot 2) hn c
  intro x y he
  exact hi (congrArg e he)

/-- The selected row has natural-plus-dual coordinates for the original
L/O₂(L) projection and its literal conjugation on the original T-orbit. -/
theorem doubledOrbit_component_marking_of_row
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (a : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype) (naturalPlusDual n)) :
    ∃ n, (n = 4 ∨ n = 5) ∧
      ∃ e : (L ⧸ pCore 2 L) ≃* LinearGroup n,
      ∃ c : componentOrbit V (T : Subgroup G) ≃* Multiplicative (CoordinateSpace n),
      ∀ (l : L) (w : componentOrbit V (T : Subgroup G)),
        ((c.symm (Multiplicative.ofAdd
          (naturalDualRepresentation (e (QuotientGroup.mk' (pCore 2 L) l))
            (c w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹ := by
  let q := D.orbitComponentQuotientHom h
  let eq : (L ⧸ pCore 2 L) ≃* D.orbitComponent := MulEquiv.ofBijective q
    ⟨D.doubledOrbit_projection_injective h hn a.groupEquiv,
      D.orbitComponentQuotientHom_surjective h⟩
  let e := (eq.trans a.groupEquiv).trans (slEquivLinear n)
  let s := D.sourceOrbitCoordinates
  let f := MulEquiv.subgroupCongr D.sourceOrbit_eq
  let c : componentOrbit V (T : Subgroup G) ≃* Multiplicative (CoordinateSpace n) :=
    f.symm.trans (s.toAddEquiv.toMultiplicative.symm.trans
      a.linearEquiv.toAddEquiv.toMultiplicative)
  refine ⟨n,hn,e,c,?_⟩
  intro l w
  have he (x : D.orbitSpace) :
      naturalDualRepresentation (e (QuotientGroup.mk' (pCore 2 L) l))
          (a.linearEquiv x) = a.linearEquiv (D.orbitRepresentation (D.orbitComponentHom l) x) := by
    change naturalDualRepresentation (slEquivLinear n (a.groupEquiv (D.orbitComponentHom l)))
      (a.linearEquiv x) = _
    exact ModuleClassification.DoubledOrbit.naturalDual_linear_intertwines
      (D.orbitRepresentation.comp D.orbitComponent.subtype) a (D.orbitComponentHom l) x
  let x := s.symm (Additive.ofMul (f.symm w))
  have hi : a.linearEquiv.symm (naturalDualRepresentation
      (e (QuotientGroup.mk' (pCore 2 L) l)) (a.linearEquiv x)) =
      D.orbitRepresentation (D.orbitComponentHom l) x :=
    a.linearEquiv.symm_apply_eq.mpr (he x)
  have hg : ((s (D.orbitRepresentation (D.orbitComponentHom l) x)).toMul : G) =
      (l : G) * ((s x).toMul : G) * (l : G)⁻¹ :=
    congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G))
      (D.doubledOrbit_component_action l x)
  have hx : ((s x).toMul : G) = (w : G) :=
    congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G))
      (s.apply_symm_apply (Additive.ofMul (f.symm w)))
  exact (congrArg (fun y : D.orbitSpace => ((s y).toMul : G)) hi).trans
    (hg.trans (congrArg (fun z : G => (l : G) * z * (l : G)⁻¹) hx))

/-- The actual FF hypotheses supply the original quotient marking and its
literal conjugation coordinates on the whole doubled orbit. -/
theorem doubledOrbit_component_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ n, (n = 4 ∨ n = 5) ∧
      ∃ e : (L ⧸ pCore 2 L) ≃* LinearGroup n,
      ∃ c : componentOrbit V (T : Subgroup G) ≃* Multiplicative (CoordinateSpace n),
      ∀ (l : L) (w : componentOrbit V (T : Subgroup G)),
        ((c.symm (Multiplicative.ofAdd
          (naturalDualRepresentation (e (QuotientGroup.mk' (pCore 2 L) l))
            (c w).toAdd))) : G) = (l : G) * (w : G) * (l : G)⁻¹ := by
  obtain ⟨n,hn,⟨a⟩⟩ := D.doubledOrbit_naturalPlusDual h hd hff
  exact D.doubledOrbit_component_marking_of_row h hn a
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
