module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.ParabolicCoordinates
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Native Mathieu calculations on literal conjugation quotients

A binary linear equivalence marks the actual quotient U/Z(U) by the native
column module. Its explicit conjugation equation transports the proved cubic
calculation: the moved image of the marked line is its F₄-point and has order
four. The existing extraspecial theorem then proves that the first source
actor O²(O₂,₃(H)) moves a subgroup of order eight, including the central kernel.
The Borel residual is excluded from Y when its native position is in the
literal centralizer of the marked point. The first moved point also lies in
the checked native totally singular six-space.

These are source adapters for Aschbacher–Smith 14.4.12, printed pp.1011–1012.
The actor positions and equivariant Sylow marking are explicit inputs; no
fixed-space record or unconnected group-family tag supplies them. Their native
construction and the remaining second-actor/radical calculations are required
before assembling the full source theorem.
-/

@[expose] public section

noncomputable section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu.M22TripleCover
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry
variable {G Q : Type*} [Group G] [Group Q] [IsMulCommutative Q]
  [Module (ZMod 2) (Additive Q)]

def coordinateRepresentation (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) :
    Representation (ZMod 2) Native.Group (Additive Q) :=
  (e.symm.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp Native.representation

theorem coordinateRepresentation_apply (e : Additive Q ≃ₗ[ZMod 2] BinarySpace)
    (g : Native.Group) (v : Additive Q) :
    coordinateRepresentation e g v = e.symm (Native.representation g (e v)) := rfl

theorem scalar_quotientImage_in_coordinates
    (U P X : Subgroup G) (hn : X ≤ normalizer (U : Set G)) (hPU : P ≤ U)
    (q : U →* Q) (hq : Function.Surjective q)
    (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) (f : X →* Native.Group)
    (hact : ∀ (x : X) (u : U), Native.representation (f x) (e (Additive.ofMul (q u))) =
      e (Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩)))
    (v : BinarySpace) (hmark : (quotientImage U q P).map e.toLinearMap = Native.binaryLine v)
    (hactor : f.range = zpowers Native.centralScalar) :
    (quotientImage U q (movedSpace P X)).map e.toLinearMap = Native.binaryPoint v := by
  have hact' : ∀ (x : X) (u : U), coordinateRepresentation e (f x) (Additive.ofMul (q u)) =
      Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩) := by
    intro x u
    rw [coordinateRepresentation_apply, hact, e.symm_apply_apply]
  rw [movedSpace, quotientImage_commutator (coordinateRepresentation e) U P X hn hPU f q hq hact']
  have ht : ∀ (g : Native.Group) (w : Additive Q),
      Native.representation g (e w) = e (coordinateRepresentation e g w) := by
    intro g w
    rw [coordinateRepresentation_apply, e.apply_symm_apply]
  have hm := subspaceCommutator_map_embedding Native.representation
    (coordinateRepresentation e) (MonoidHom.id Native.Group) e.toLinearMap ht
    f.range (quotientImage U q P)
  simp only [Subgroup.map_id] at hm
  rw [← hm, hmark, hactor, Native.scalar_moved_line_eq_point]

theorem scalar_quotientImage_card_four
    (U P X : Subgroup G) (hn : X ≤ normalizer (U : Set G)) (hPU : P ≤ U)
    (q : U →* Q) (hq : Function.Surjective q)
    (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) (f : X →* Native.Group)
    (hact : ∀ (x : X) (u : U), Native.representation (f x) (e (Additive.ofMul (q u))) =
      e (Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩)))
    (v : BinarySpace) (hv : v ≠ 0)
    (hmark : (quotientImage U q P).map e.toLinearMap = Native.binaryLine v)
    (hactor : f.range = zpowers Native.centralScalar) :
    Nat.card (((movedSpace P X).subgroupOf U).map q) = 4 := by
  let b := Submodule.equivMapOfInjective e.toLinearMap e.injective
    (quotientImage U q (movedSpace P X))
  have hc : Nat.card (quotientImage U q (movedSpace P X)) = 4 := by
    rw [Nat.card_congr b.toEquiv,
      scalar_quotientImage_in_coordinates U P X hn hPU q hq e f hact v hmark hactor,
      Native.binaryPoint_card hv]
  let ec : (((movedSpace P X).subgroupOf U).map q) ≃
      quotientImage U q (movedSpace P X) := {
    toFun u := ⟨Additive.ofMul u, u.property⟩
    invFun u := ⟨u.val.toMul, u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr ec).trans hc

theorem firstActor_movedSpace_card_eight [Finite G]
    (H T U V₂ : Subgroup G) [IsExtraspecial 2 U]
    (hX : firstActor H ∈ XFamily H T) (hUT : U ≤ T)
    (hHU : H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U)
    (q : U →* Q) (hq : Function.Surjective q) (hker : q.ker = center U)
    (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) (f : firstActor H →* Native.Group)
    (hact : ∀ (x : firstActor H) (u : U),
      Native.representation (f x) (e (Additive.ofMul (q u))) =
      e (Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp (hX.le_H.trans hHU) x x.property u u.property⟩)))
    (v : BinarySpace) (hv : v ≠ 0)
    (hmark : (quotientImage U q V₂).map e.toLinearMap = Native.binaryLine v)
    (hactor : f.range = zpowers Native.centralScalar) :
    Nat.card (movedSpace V₂ (firstActor H)) = 8 := by
  apply movedSpace_card_eight_of_extraspecial_image H T U V₂ (firstActor H)
    hX hUT hHU hVU hZV q hker
  exact scalar_quotientImage_card_four U V₂ (firstActor H) (hX.le_H.trans hHU)
    hVU q hq e f hact v hv hmark hactor

theorem borelActor_not_mem_YFamily_of_native_position [Finite G]
    (H T U V₂ E B : Subgroup G)
    (hn : borelActor B ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (q : U →* Q) (hsmall : Nat.card q.ker < 8)
    (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) (f : borelActor B →* Native.Group)
    (hact : ∀ (x : borelActor B) (u : U),
      Native.representation (f x) (e (Additive.ofMul (q u))) =
      e (Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩)))
    (hmark : (quotientImage U q V₂).map e.toLinearMap = Native.binaryLine Native.markedVector)
    (hactor : f.range ≤ Native.pointCentralizer) :
    borelActor B ∉ YFamily H T V₂ E := by
  refine not_mem_YFamily_of_fixed_quotient_point (coordinateRepresentation e)
    H T U V₂ E (borelActor B) hn hVU f q ?_ (quotientImage U q V₂) ?_ hsmall ?_
  · intro x u
    rw [coordinateRepresentation_apply, hact, e.symm_apply_apply]
  · intro u hu
    change q u ∈ (V₂.subgroupOf U).map q
    exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
  · intro w hw a
    have hm : e w ∈ Native.binaryLine Native.markedVector := by
      rw [← hmark]
      exact Submodule.mem_map_of_mem hw
    have hf := (hactor a.property).2 (e w) hm
    change coordinateRepresentation e (a : Native.Group) w = w
    rw [coordinateRepresentation_apply, hf, e.symm_apply_apply]

theorem firstActor_image_le_native_parabolic
    (U V₂ : Subgroup G) (H : Subgroup G)
    (hn : firstActor H ≤ normalizer (U : Set G)) (hVU : V₂ ≤ U)
    (q : U →* Q) (hq : Function.Surjective q)
    (e : Additive Q ≃ₗ[ZMod 2] BinarySpace) (f : firstActor H →* Native.Group)
    (hact : ∀ (x : firstActor H) (u : U),
      Native.representation (f x) (e (Additive.ofMul (q u))) =
      e (Additive.ofMul (q ⟨(x : G) * u * (x : G)⁻¹,
        le_normalizer_iff.mp hn x x.property u u.property⟩)))
    (hmark : (quotientImage U q V₂).map e.toLinearMap = Native.binaryLine Native.markedVector)
    (hactor : f.range = zpowers Native.centralScalar) :
    (quotientImage U q (movedSpace V₂ (firstActor H))).map e.toLinearMap ≤
      Native.parabolicSpace := by
  rw [scalar_quotientImage_in_coordinates U V₂ (firstActor H) hn hVU q hq e f hact
    Native.markedVector hmark hactor]
  exact Native.markedPoint_le_parabolic

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry
