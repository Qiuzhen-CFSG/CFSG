module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceRecognition
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Assembly

/-!
# Recognizing the geometry on the original binary quotient

The source natural/Weyl recognition gives an equivariant linear marking.
Its group form identifies the literal U/V₁ quotient, including conjugation
by the original H. Transporting the octonion hexagon through this marking
proves its metric properties and the absence of a four-cycle.

This supplies the geometry in 14.7.55(7) from 14.7.54; the marked source
point, the critical-pair symmetry and the endpoint still require their
separate source deductions. Earlier action, structural and F.9.18 inputs
remain explicit as in G2SourceRecognition.

Source: Aschbacher–Smith, 14.7.54–55, printed pp.1065–1066.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
open G2Exclusion G2Exclusion.MarkedGeometry
open G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

variable [(F.Vi 1).subgroupOf F.U |>.Normal]

/-- The linear identification identifies the literal group quotient. -/
def literalModuleEquiv (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W) :
    Multiplicative m.Space ≃* (F.U ⧸ (F.Vi 1).subgroupOf F.U) :=
  E.toAddEquiv.toMultiplicative.trans c.quotientEquiv.symm

omit [Finite G] in
theorem literalModuleEquiv_coordinates (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (u : F.U) :
    E (((literalModuleEquiv c m E).symm (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u)).toAdd) =
      (c.coordinates u).toAdd := by
  change E (E.symm ((c.quotientEquiv (QuotientGroup.mk' _ u)).toAdd)) = _
  rw [E.apply_symm_apply,c.quotientEquiv_mk]

omit [Finite G] in
/-- The original conjugation action, in the recognized natural/Weyl coordinates. -/
theorem literalModuleEquiv_conjugation
    (i : HStar F.H →* Atlas.G2.Model (ZMod 2))
    (m : BinaryG2Module) (E : m.Space ≃ₗ[ZMod 2] W)
    (he : ∀ a v, E (m.action (i a) v) = σ a (E v))
    (a : F.H) (u : F.U) :
    m.action (i (starMap F a))
      (((literalModuleEquiv c m E).symm (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u)).toAdd) =
      ((literalModuleEquiv c m E).symm (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)
        ⟨a * (u : G) * (a : G)⁻¹,
          (mem_normalizer_iff.mp (c.normalized a.property) u).mp u.property⟩)).toAdd := by
  apply E.injective
  rw [he,literalModuleEquiv_coordinates,literalModuleEquiv_coordinates]
  exact (c.equivariant a u).symm

/-- The original source recognition constructs the quotient geometry and
its full equivariance; the no-four-cycle assertion is then a model theorem. -/
theorem source_quotient_geometry
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
    ∃ i : HStar F.H →* Atlas.G2.Model (ZMod 2), Function.Injective i ∧
      commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range ∧
    ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      (∀ a v, E (m.action (i a) v) = σ a (E v)) ∧
      (∀ (a : F.H) (u : F.U), m.action (i (starMap F a))
        (((literalModuleEquiv c m E).symm (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U) u)).toAdd) =
        ((literalModuleEquiv c m E).symm (QuotientGroup.mk' ((F.Vi 1).subgroupOf F.U)
          ⟨a * (u : G) * (a : G)⁻¹,
            (mem_normalizer_iff.mp (c.normalized a.property) u).mp u.property⟩)).toAdd) ∧
      Assembly.HexagonConclusions
        (transportGeometry m.singularMap.geometry (literalModuleEquiv c m E)) := by
  obtain ⟨i,hi,hcontains,hE⟩ := source_natural_or_weyl c h hab hcomponent hfit eK hf
    P hP orbit path hplace selection hquad hbound
  have hm : ∃ m : BinaryG2Module, ∃ E : m.Space ≃ₗ[ZMod 2] W,
      ∀ a v, E (m.action (i a) v) = σ a (E v) := by
    rcases hE with ⟨E,hE⟩ | ⟨E,hE⟩
    · exact ⟨.natural,E,hE⟩
    · exact ⟨.weyl,E,hE⟩
  obtain ⟨m,E,hE⟩ := hm
  exact ⟨i,hi,hcontains,m,E,hE,literalModuleEquiv_conjugation c i m E hE,
    realizedIncidence_girth _,realizedIncidence_diameter _,realizedCollinearity_no_four_cycle _⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
