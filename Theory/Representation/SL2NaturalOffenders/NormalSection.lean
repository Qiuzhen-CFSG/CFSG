module
public import Theory.Representation.BinaryOffender.NormalLayerQuotient
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.SL2NaturalOffenders.Ratios
/-!
# Best offenders inside a normal natural SL2 section

A faithful natural quotient of an invariant subspace extends to a faithful
full action when its normal actor is self-centralizing. Original best
offenders remain offenders on this quotient. The natural SL2 offender
calculation puts each in the normal actor, so the entire offender group lies
there. The literal 13.6.18 consumer applies this to its original moved section.
Source: Aschbacher--Smith B.6.9 and E.2.3, printed pp.115--116 and216--217.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {G V F : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Field F] [Finite F] [Algebra (ZMod 2) F]

theorem offenderSubgroup_le_of_normal_natural_section
    (ρ : Representation (ZMod 2) G V)
    (C : Subgroup G) [C.Normal] (hC : centralizer (C : Set G) ≤ C)
    (e : C ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hF : 2 < Nat.card F)
    (U : Subrepresentation ρ)
    (f : U.toSubmodule →ₗ[ZMod 2] (Fin 2 → F)) (hf : Function.Surjective f)
    (hk : f.ker = fixedSpace U.toRepresentation C)
    (he : ∀ (g : C) w, f (U.toRepresentation (g : G) w) =
      NoStrong.natural (F := F) (e g) (f w)) :
    offenderSubgroup ρ ≤ C := by
  let σ := (NoStrong.natural (F := F)).comp e.toMonoidHom
  have hσ : Function.Injective σ := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    exact LinearMap.congr_fun hab w
  obtain ⟨τ,hτ,hfull,hnat⟩ := exists_faithful_action_of_normal_layer_quotient
    U.toRepresentation C hC σ hσ f hf hk he
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA,_⟩
  have hAτ : IsOffender τ A := ⟨hA.1,
    (fixedCodim_le_of_equivariant_surjection U.toRepresentation τ f hf hfull A).trans
      ((fixedCodim_subrepresentation_le ρ U A).trans (hA.isOffender ρ).2)⟩
  obtain ⟨T,hAT⟩ := hA.1.2.isPGroup.exists_le_sylow
  exact ((Ratios.offender_iff_eq_sylowInf C e τ (fun g w => hnat g w)
    hF hτ T hAT).mp hAτ).le.trans inf_le_right
end Representation.SL2NaturalOffenders
