module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.ExceptionalSplitting.Preparation

/-!
# Ambient reconstruction from the second-action complement

A complement for the ambient G₂-action contained in V₂=C_V(G₁) is
G-invariant by the actual product decomposition. The restriction of the
original quotient map identifies it with V₂/C_V(G), so the complete B.4.8(3)
record transports to this ambient submodule. The resulting fixed-supplement
equality is exactly the premise of `adequate_of_exceptional_fixed_supplement`
in NonsplitCase.

The existence of the second-action complement is still an intermediate
obligation. Preparation states the literal chief-flag applicability and
independently proves the quotient transport, model identification, faithfulness
and four-space structure needed for that argument. B.4.8(4) gives a bound on
indecomposable constituents only after those flags are supplied. This file does
not treat a four-dimensional fixed quotient as an existing ambient complement.

The only earlier-source input used here is full `EarlierB48Three`, owned by
qt-b-04-natural-extensions. The remaining constituent and complement producers
are intermediate proof work owned by this task and its prerequisites, not
additional earlier-source assumptions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(3)–(4),
printed p.91, and the final B.5.6 proof, printed p.110.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
namespace ExceptionalSplitting
open ComponentReduction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Restrict the original global fixed-quotient map to the constructed ambient
submodule. Its bijectivity uses the given complement, not a choice of quotient
coordinates. -/
noncomputable def ambientComplementEquiv (c : Conclusion ρ)
    (S : Subrepresentation (secondAmbientAction c)) (hS : S ≤ secondUpper c)
    (hc : IsCompl S.toSubmodule (secondAmbientAction c).invariants) :
    ActionEquiv ((ambientModule c S hS).toRepresentation.comp (second c).subtype)
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp
        (second c).subtype) := by
  let Q := (fixed ρ).quotientImage c.productConfiguration.fixed
  let p : S.toSubmodule →ₗ[ZMod 2] Q.toSubmodule :=
    { toFun := fun x => ⟨ρ.invariants.mkQ x,⟨x,hS x.property,rfl⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hi : Function.Injective p := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    have hq : ρ.invariants.mkQ (a : V) = ρ.invariants.mkQ (b : V) :=
      congrArg Subtype.val hab
    have hz : (a : V) - b ∈ ρ.invariants := (Submodule.Quotient.eq ρ.invariants).mp hq
    exact Submodule.disjoint_def.mp hc.disjoint _
      (S.toSubmodule.sub_mem a.property b.property) (fun g => hz g)
  have hs : Function.Surjective p := by
    rintro ⟨v,a,ha,rfl⟩
    have ham : a ∈ S.toSubmodule ⊔ (secondAmbientAction c).invariants := by
      rw [hc.sup_eq_top]
      trivial
    obtain ⟨x,hx,z,hz,hxz⟩ := Submodule.mem_sup.mp ham
    have hzR : z ∈ c.productConfiguration.fixed.toSubmodule := by
      have h := c.productConfiguration.fixed.toSubmodule.sub_mem ha (hS hx)
      rw [← hxz] at h
      simpa only [add_sub_cancel_left] using h
    have hzg : z ∈ ρ.invariants := (second_invariants_iff c ⟨z,hzR⟩).mp
      (fun g => Subtype.ext (hz g))
    refine ⟨⟨x,hx⟩,?_⟩
    apply Subtype.ext
    change ρ.invariants.mkQ x = ρ.invariants.mkQ a
    rw [← hxz,map_add,show ρ.invariants.mkQ z = 0 from
      (Submodule.Quotient.mk_eq_zero _).mpr hzg,add_zero]
  exact ⟨MulEquiv.refl _,LinearEquiv.ofBijective p ⟨hi,hs⟩,fun _ _ => rfl⟩

/-- Reconstruct the requested ambient submodule and every B.4.8(3) clause once
the independent constituent argument has supplied the G₂-complement. -/
theorem ambient_splitting_of_complement [Finite G] [FiniteDimensional (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c))
    (q : FourDimensionalSource (secondFactorAction c f))
    (S : Subrepresentation (secondAmbientAction c)) (hS : S ≤ secondUpper c)
    (hc : IsCompl S.toSubmodule (secondAmbientAction c).invariants) :
    ∃ W₂ : Subrepresentation ρ,
      W₂.toSubmodule ≤ c.productConfiguration.fixed.toSubmodule ∧
      IsCompl W₂.toSubmodule (fixedSpace ρ (second c)) ∧
      Nonempty (FourDimensionalSource (W₂.toRepresentation.comp (second c).subtype)) := by
  obtain ⟨q'⟩ := four_source_transport h48 (actionSymm (factorQuotientEquiv c f)) q
  refine ⟨ambientModule c S hS,hS,hc,?_⟩
  exact four_source_transport h48 (ambientComplementEquiv c S hS hc) q'

/-- The exact equality consumed by the existing two-factor assembly. -/
theorem fixed_supplement_of_complement (c : Conclusion ρ)
    (S : Subrepresentation (secondAmbientAction c)) (hS : S ≤ secondUpper c)
    (hc : IsCompl S.toSubmodule (secondAmbientAction c).invariants) :
    fixedSpace ρ (second c) ⊔ c.productConfiguration.fixed.toSubmodule = ⊤ := by
  apply top_unique
  rw [← hc.symm.sup_eq_top]
  exact sup_le_sup_left
    (show S.toSubmodule ≤ c.productConfiguration.fixed.toSubmodule from hS) _

end ExceptionalSplitting
end CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
