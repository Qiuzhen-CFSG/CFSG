module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceMarkedGeometry
public import Theory.Representation.G2BinaryModelOffenders

/-!
# Discharging the concrete G₂ model premises in the source geometry

The natural/Weyl rank bounds and best-offender classification now come from
the actual octonion models. The source application retains the original
section, critical path, quotient map, point and line; none of the four model
premises of the earlier marked-geometry interface remains an assumption.

The earlier faithful action, generalized-Fitting and F.9.18 inputs remain
with the final source assembly. The critical-actor identification and the
14.7.60–62 argument remain obligations of this G₂ exclusion branch.

Source: Aschbacher–Smith B.4.6 and 14.7.54–55, printed pp.88–90,1065–1066.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit

/-- Small elementary actors cannot offend on either recognized model. -/
theorem model_small_rank_bound (m : BinaryG2Module)
    (A : Subgroup (Atlas.G2.Model (ZMod 2))) (hA : IsElementaryTwo A)
    (hr : rank A < 3) : rank A < fixedCodim m.action A := by
  cases m with
  | natural => exact Atlas.G2.Natural.BinaryModelOffenders.natural_small_rank_bound A hA hr
  | weyl => exact Atlas.G2.Natural.BinaryModelOffenders.weyl_small_rank_bound A hA hr

/-- Both recognized models have exactly the marked elementary-eight offenders. -/
theorem model_bestOffender (m : BinaryG2Module)
    (A : Subgroup (Atlas.G2.Model (ZMod 2))) :
    IsBestOffender m.action A ↔ ∃ g : Atlas.G2.Model (ZMod 2),
      Atlas.G2.BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = A := by
  cases m with
  | natural => exact Atlas.G2.Natural.BinaryModelOffenders.natural_bestOffender A
  | weyl => exact Atlas.G2.Natural.BinaryModelOffenders.weyl_bestOffender A

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

/-- All eight marked-geometry clauses on the original source section, with the
four concrete numerical and offender premises fully discharged. -/
theorem source_marked_geometry_from_models
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ)
    (P : Sylow 2 (HStar F.H)) (hP : star F (K F) ⊔ (P : Subgroup (HStar F.H)) = ⊤)
    (orbit : letI : (star F (K F)).Normal := hfit ▸ inferInstance
      letI : Finite W := Finite.of_surjective (fun x : F.U => (c.coordinates x).toAdd)
        (Multiplicative.toAdd.surjective.comp c.onto)
      OrbitInputs σ (star F (K F)) P hP)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (hquad : IsQuadratic σ (star F path.Uα))
    (hbound : fixedCodim σ (star F path.Uα) ≤ 2 * rank (star F path.Uα)) :
    letI : IsMulCommutative V := h.chosen.elementary.toIsMulCommutative
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
      (letI := internalModuleAction c i m E
      ∃ p : Atlas.G2.SingularPoints (ZMod 2),
        MarkedPencil.Assembly.SourceConclusions (F.U.subgroupOf F.H)
          ((F.Vi 1).subgroupOf F.H) ((F.Vi 2).subgroupOf F.H) (V.subgroupOf F.H)
          m.action m.singularMap (internalModuleEquiv c m E) (starMap F) i
          (T.subtype (F.invariant 1)) p ∧
        Assembly.HexagonConclusions (transportGeometry m.singularMap.geometry
          (internalModuleEquiv c m E)) ∧
        (letI := c.kernel_normal
        (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).point p =
          ((F.Vi 2).subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) ∧
        ∃ l : Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.ZeroProductLine (ZMod 2),
          (V.subgroupOf F.U).map (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)) =
            (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)).line l ∧
          Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.pointOnLine p l)) := by
  apply source_marked_geometry c h hab hcomponent hfit eK hf P hP orbit path hplace
    selection hquad hbound
  · exact Atlas.G2.Natural.BinaryModelOffenders.rank_le_two
  · intro m A hA hr
    have hh := model_small_rank_bound m A hA (by omega)
    omega
  · intro m A _ hA hr
    have hh := model_small_rank_bound m A hA (by omega)
    omega
  · exact model_bestOffender

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
