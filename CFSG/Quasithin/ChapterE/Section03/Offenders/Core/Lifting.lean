module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Lifting subgroups of an induced automizer

A subgroup of the actual image of `A` acting on `V` lifts to its inverse
image in `A`, with the same relative index. This identifies the quotient
rank used in the dual generated core with the corank of an ambient subgroup.

The proof takes the inverse image under the normalizer action, intersects
with `A`, and uses the relative-index formula for inverse images. The fixed
elements of a lifted action are exactly the ambient centralizer of the lift.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the argument
for E.3.31–32, printed pp. 237–238. The construction also appears privately
in `Section03.Parameters` in the fixed-space-family proof.
-/

public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G]

/-- An automizer subgroup lifts to an ambient subgroup with the same binary
quotient corank. The lift is the full inverse image inside `A`. -/
theorem core_lift_image_subgroup {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G))
    (D : Subgroup (Automizer V)) (hD : D ≤ inducedAutomizer V A) :
    ∃ B ≤ A, inducedAutomizer V B = D ∧
      subgroupCorank A B = Nat.log 2 (D.relIndex (inducedAutomizer V A)) := by
  let N := normalizer (V : Set G)
  let f := V.normalizerMonoidHom.rangeRestrict
  let C := A.subgroupOf N
  let L := C ⊓ D.comap f
  let B := L.map N.subtype
  have hBA : B ≤ A := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1
  have hBN : B.subgroupOf N = L := by
    exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective L
  have hmap : L.map f = D := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro d hd
      obtain ⟨x, hx, he⟩ := hD hd
      exact ⟨x, ⟨hx, (show f x ∈ D from he.symm ▸ hd)⟩, he⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · change (B.subgroupOf N).map f = D
    rw [hBN, hmap]
  · unfold subgroupCorank
    congr 1
    rw [← Subgroup.relIndex_subgroupOf (H := B) hA, hBN]
    exact (Subgroup.inf_relIndex_left C (D.comap f)).trans
      (Subgroup.relIndex_comap D f C)

/-- A subgroup of the induced image, regarded as a group in its own right,
lifts with its ordinary index equal to the relative index in `A`. -/
theorem core_lift_induced_subgroup {V A : Subgroup G}
    (hA : A ≤ normalizer (V : Set G)) (X : Subgroup (inducedAutomizer V A)) :
    ∃ B ≤ A, inducedAutomizer V B = X.map (inducedAutomizer V A).subtype ∧
      subgroupCorank A B = Nat.log 2 X.index := by
  let I := inducedAutomizer V A
  obtain ⟨B, hBA, hBI, hcor⟩ := core_lift_image_subgroup hA
    (X.map I.subtype) (Subgroup.map_subtype_le X)
  have hind : (X.map I.subtype).relIndex I = X.index := by
    simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Subgroup.relIndex_top_right] using
      Subgroup.relIndex_map_map_of_injective X ⊤ I.subtype_injective
  exact ⟨B, hBA, hBI, hind ▸ hcor⟩

/-- Fixed elements for a subgroup of the actual action image centralize any
ambient lift of that subgroup, and conversely. -/
theorem core_fixed_iff_centralizer {V B : Subgroup G}
    (hB : B ≤ normalizer (V : Set G))
    (I : Subgroup (Automizer V)) (X : Subgroup I)
    (hX : inducedAutomizer V B = X.map I.subtype) (v : V) :
    (∀ x ∈ X, ((Automizer V).subtype.comp I.subtype) x v = v) ↔
      (v : G) ∈ centralizer (B : Set G) := by
  constructor
  · intro hv b hb
    have hbI : V.normalizerMonoidHom.rangeRestrict ⟨b, hB hb⟩ ∈
        inducedAutomizer V B := ⟨⟨b, hB hb⟩, hb, rfl⟩
    rw [hX] at hbI
    obtain ⟨x, hx, he⟩ := hbI
    have hf : V.normalizerMonoidHom ⟨b, hB hb⟩ v = v := by
      change ((V.normalizerMonoidHom.rangeRestrict ⟨b, hB hb⟩ : Automizer V) : MulAut V) v = v
      rw [← he]
      exact hv x hx
    exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : V => (z : G)) hf)
  · intro hv x hx
    have hxB : (x : Automizer V) ∈ inducedAutomizer V B := by
      rw [hX]
      exact ⟨x, hx, rfl⟩
    obtain ⟨b, hb, he⟩ := hxB
    change ((x : Automizer V) : MulAut V) v = v
    rw [← he]
    apply Subtype.ext
    change (b : G) * (v : G) * (b : G)⁻¹ = (v : G)
    rw [hv b hb, mul_inv_cancel_right]

end CFSG.Quasithin.ChapterE
