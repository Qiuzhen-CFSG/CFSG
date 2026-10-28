module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Rows
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Transport

/-!
# The complementary submodule inside the original ambient action

A G₂-submodule of V₂=C_V(G₁) is G-invariant because G=G₁G₂. Its image
under V₂ ↪ V supplements C_V(G) inside V₂. When V=[V,L]+V₂, the original
inclusion also identifies the local moved space with [V,G₂]. Thus the
natural and doubled factor rows retain the precise moved space required
by B.5.6(3), while the exceptional row retains its moved-space containment.

The literal fixed-quotient comparisons already proved in the exceptional
extension's transport leaf apply without an exceptionality hypothesis. We
reuse them to transport the extracted factor action to this ambient image.
For the four-dimensional row, the full B.4.8(3) implication is applied with
all its hypotheses proved on the transported action. Its source producer
is qt-b-04-natural-extensions, with discharge retained by final assembly.

The consumer is B.5.12's supplemented branch. Source: Aschbacher–Smith,
combined manuscript of 1 March 2004, B.5.11–12, printed p.109, with the
fixed-quotient convention of B.5.6(3), printed p.105.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences ComponentReduction
open ExceptionalExtension
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

noncomputable def ambientSpace (c : Conclusion ρ)
    (U : Subrepresentation (secondAction c)) : Subrepresentation ρ where
  toSubmodule := U.toSubmodule.map c.productConfiguration.fixed.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    obtain ⟨x,hx,rfl⟩ := hv
    obtain ⟨a,b,rfl⟩ := c.productConfiguration.product.exists_mul g
    refine ⟨(secondAction c) b x,U.apply_mem_toSubmodule b hx,?_⟩
    change ρ (b : G) x = ρ ((a : G) * (b : G)) x
    rw [map_mul, Module.End.mul_apply]
    have hz := ((secondAction c) b x).property
    change ρ (b : G) x ∈ c.productConfiguration.fixed.toSubmodule at hz
    have hf : ρ (b : G) x ∈ fixedSpace ρ c.first := c.productConfiguration.fixed_eq.le hz
    exact (hf a).symm

theorem ambientSpace_supplement (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    (ambientSpace c f.space).toSubmodule ⊔ ρ.invariants =
      c.productConfiguration.fixed.toSubmodule := by
  apply le_antisymm
  · apply sup_le
    · rintro v ⟨x,_,rfl⟩
      exact x.property
    · exact invariants_le_fixed c
  · intro v hv
    have ht : (⟨v,hv⟩ : c.productConfiguration.fixed.toSubmodule) ∈
        f.space.toSubmodule ⊔ Representation.invariants (secondAction c) := by
      rw [f.supplement]
      trivial
    obtain ⟨w,hw,z,hz,h⟩ := Submodule.mem_sup.mp ht
    exact Submodule.mem_sup.mpr ⟨w,⟨w,hw,rfl⟩,z,
      (Nonsplit.second_invariants_iff c z).mp hz,congrArg Subtype.val h⟩

/-- In the supplemented configuration, the complementary moved space is
exactly the image of its moved space on V₂ under the original inclusion. -/
theorem second_moved_map_of_supplement (c : Conclusion ρ)
    (hs : c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule = ⊤) :
    (moved (secondAction c) ⊤).map c.productConfiguration.fixed.toSubmodule.subtype =
      moved ρ (second c) := by
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact Submodule.subset_span ⟨g,g.property,v,Submodule.mem_top,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,hg,v,_,rfl⟩
    obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp
      (hs.symm ▸ Submodule.mem_top (x := v))
    let x : c.productConfiguration.fixed.toSubmodule := ⟨z,hz⟩
    refine ⟨(secondAction c) ⟨g,hg⟩ x - x,
      Submodule.subset_span ⟨(⟨g,hg⟩ : second c),mem_top _,x,Submodule.mem_top,rfl⟩,?_⟩
    change ρ g z - z = ρ g (w+z) - (w+z)
    rw [map_add, show ρ g w = w from first_fixed_by_second c hw ⟨g,hg⟩]
    abel

theorem ambient_image_eq (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    ((fixed ρ).quotientImage c.productConfiguration.fixed).toSubmodule =
      ((fixed ρ).quotientImage (ambientSpace c f.space)).toSubmodule := by
  change c.productConfiguration.fixed.toSubmodule.map ρ.invariants.mkQ =
    (ambientSpace c f.space).toSubmodule.map ρ.invariants.mkQ
  have he := congrArg (fun S : Submodule (ZMod 2) V => S.map ρ.invariants.mkQ)
    (ambientSpace_supplement c f)
  simpa only [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq] using he.symm

noncomputable def ambientFactorEquiv (c : Conclusion ρ)
    (f : FactorModuleConclusion (secondAction c)) :
    ActionEquiv (((fixed (secondAction c)).quotientImage f.space).toRepresentation.comp
      (⊤ : Subgroup (second c)).subtype)
      (((fixed ρ).quotientImage (ambientSpace c f.space)).toRepresentation.comp
        (second c).subtype) := by
  let e : ActionEquiv
      (((fixed ρ).quotientImage c.productConfiguration.fixed).toRepresentation.comp
        (second c).subtype)
      (((fixed ρ).quotientImage (ambientSpace c f.space)).toRepresentation.comp
        (second c).subtype) :=
    ⟨MulEquiv.refl _, LinearEquiv.ofEq _ _ (ambient_image_eq c f), fun _ _ => rfl⟩
  exact transAction (Nonsplit.factorQuotientEquiv c f) e

/-- Lift the actual B.5.11 module through V₂ ↪ V. In the supplement branch
its natural and doubled spaces are literally [V,G₂], and the exceptional
row retains every B.4.8(3) conclusion on its original quotient image. -/
theorem ambient_factor_case [Finite G] [Module.Finite (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (c : Conclusion ρ)
    (hs : c.sectionData.space.toSubmodule ⊔ c.productConfiguration.fixed.toSubmodule = ⊤)
    (f : FactorModuleConclusion (secondAction c)) :
    SourceFactorCase ρ (second c) (ambientSpace c f.space) := by
  have he := actionSymm (ambientFactorEquiv c f)
  cases f.actionCase with
  | natural hm hn =>
    apply SourceFactorCase.natural
    · change f.space.toSubmodule.map _ = _
      rw [hm,second_moved_map_of_supplement c hs]
    · cases hn with
      | linearTwo F hn => exact .linearTwo F ⟨transAction he hn.some⟩
      | linearThree F ho hn => exact .linearThree F ho ⟨transAction he hn.some⟩
      | symmetricFive hn => exact .symmetricFive ⟨transAction he hn.some⟩
  | doubleNatural F ho hm hn =>
    apply SourceFactorCase.doubleNatural F ho
    · change f.space.toSubmodule.map _ = _
      rw [hm,second_moved_map_of_supplement c hs]
    · exact ⟨transAction he hn.some⟩
  | exceptional hm h =>
    obtain ⟨q⟩ := Nonsplit.four_source_transport h48 he h
    apply SourceFactorCase.exceptional _ q
    rw [← second_moved_map_of_supplement c hs]
    exact Submodule.map_mono hm

end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction
