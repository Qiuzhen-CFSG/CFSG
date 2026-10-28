module
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.AbelianSection.Coprime
public import Mathlib.RepresentationTheory.Invariants

/-!
# The literal central subspace in the HS Frattini module

Map Z(K) into Q and then through coreMap. Its image is a binary subspace of
Qbar and is fixed by the published frattiniRepresentation. Equality with
the whole invariant space still requires the model action calculation.
Source: Aschbacher–Smith I.2.2(5), p.412 / PDF p.423.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
variable {K : Type*} [Group K] [Finite K]

/-- The center maps into Qbar using its original inclusion in K and coreMap. -/
def centralFrattiniMap
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) : center K →* Qbar e :=
  (coreMap e).comp
    { toFun := fun z => ⟨⟨z, center_le_M e z.property⟩, center_le_Q e hZ z.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem centralFrattiniMap_val
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (z : center K) :
    (centralFrattiniMap e hZ z : M e ⧸ E e) =
      QuotientGroup.mk' (E e) ⟨z, center_le_M e z.property⟩ := rfl

/-- After the inclusion Qbar ≤ M/E, this is exactly the image of the
relative central factor under the original quotient map. -/
theorem centralFrattiniMap_range_map
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    (centralFrattiniMap e hZ).range.map (Qbar e).subtype =
      (centralFactor e).map (QuotientGroup.mk' (E e)) := by
  ext x
  constructor
  · rintro ⟨v, ⟨z, rfl⟩, rfl⟩
    exact ⟨⟨z, center_le_M e z.property⟩, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨centralFrattiniMap e hZ ⟨z, hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩

/-- The literal image of Z(K), as a binary subspace of the embedded Qbar. -/
noncomputable def centralLine
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) : Submodule (ZMod 2) (Additive (Qbar e)) :=
  AddSubgroup.toZModSubmodule 2 (centralFrattiniMap e hZ).range.toAddSubgroup

theorem centralLine_le_invariants
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) :
    centralLine e hZ ≤ (frattiniRepresentation e).invariants := by
  intro v hv
  obtain ⟨z, hz⟩ : ∃ z : center K, centralFrattiniMap e hZ z = v.toMul := hv
  apply (Representation.mem_invariants _ _).mpr
  intro a
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) a
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [frattiniRepresentation_apply, ← hz, centralFrattiniMap_val]
  let zm : M e := ⟨z, center_le_M e z.property⟩
  have hc : m * zm = zm * m := by
    apply Subtype.ext
    exact mem_center_iff.mp z.property m
  have hbar := congrArg (QuotientGroup.mk' (E e)) hc
  simp only [map_mul] at hbar
  change QuotientGroup.mk' (E e) m * QuotientGroup.mk' (E e) zm *
    (QuotientGroup.mk' (E e) m)⁻¹ = QuotientGroup.mk' (E e) zm
  rw [hbar, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
