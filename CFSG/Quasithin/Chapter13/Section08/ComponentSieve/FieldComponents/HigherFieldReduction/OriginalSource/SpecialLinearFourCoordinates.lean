module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.SpecialLinearFourConstituent
public import Theory.Representation.SL3FourNaturalDual.HomogeneousOrbit

/-!
# Natural-plus-dual coordinates on the original source module

The original T*-homogeneous natural constituent and its disjoint translate
by the original inverter exhaust their full orbit: full SL₃(4) automorphism
coverage preserves the natural/dual pair. The previously proved source
saturation makes this orbit all of U_H/V₁. Summing the two actual embeddings,
with the GL₃ correction in the graph action, constructs the required binary
linear equivalence. The component inclusion and scalar center are retained.

Source: Aschbacher–Smith, 13.8.20, printed p.955, using B.4.5 and F.9.18(4,7).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender

open Representation.SL3FourNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ExceptionalFields.LinearThreeFour.AutomorphismModule
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- The original full SL₃(4) branch has the natural-plus-dual module on the
literal U_H/V₁, with its component inclusion unchanged. -/
theorem source_specialLinearThree_coordinates
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁) (eK : Source.starImage H K ≃* SL) :
    ∃ (e : Source.starImage H K ≃* SL)
      (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] Representation.SL3FourNaturalDual.V),
      ∀ (k : Source.starImage H K) v,
        E (act.representation k v) = representation (e k) (E v) := by
  obtain ⟨I,hI,e,n,_,hfull,t,_,g,ht,hdis⟩ :=
    source_specialLinearThree_natural_constituent c act eK
  let tstar := QuotientGroup.mk' (pCore 2 H)
    ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩
  have htm : tstar ∈ Source.starImage H (T : Subgroup G) :=
    ⟨⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩,t.property.1,rfl⟩
  let ts : Source.starImage H (T : Subgroup G) := ⟨tstar,htm⟩
  have hspan := HomogeneousOrbit.natural_orbit_span act.representation hI e n ts g ht
  have hcomp : IsCompl I (I.map (act.representation tstar)) :=
    ⟨hdis,codisjoint_iff.mpr (hspan.symm.trans hfull)⟩
  let d : LiteralAction H V₃ V₁ := ⟨act.representation,act.conjugation⟩
  let p : NaturalPair d K e tstar := {
    space := I
    coordinates := n.lift hI.isIrrPlus.choose_spec.1
    natural_action := n.lift_symm_equivariant hI.isIrrPlus.choose_spec.1
    complementary := hcomp }
  let m := sourceMarking d K e tstar p g ht
  refine ⟨e,m.coordinates,fun k v => ?_⟩
  have he : m.actor (e k) = k := by
    change (e.symm (e k) : Source.Hstar H) = k
    rw [e.symm_apply_apply]
  exact he ▸ m.equivariant (e k) v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
