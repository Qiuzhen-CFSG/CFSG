module

public import Theory.GroupTheory.PStar.FixedPoints.BalanceOfExtension
public import Theory.GroupAction.FixedPointHom

/-!
# Fixed-core containment under arbitrary quotient maps

Take the inverse image D of the quotient fixed subgroup. It is invariant
under the actor, and its fixed subgroup is canonically the original fixed
subgroup. Balance in D puts its fixed two-star core inside Ostar(D), whose
image lies in the quotient fixed two-star core by surjective functoriality.
This proves the required image containment without assuming D normal in the
original group or requiring the stronger equality from GLS 5.13.

Source: the containment clause of GLS II, Chapter B, Proposition 5.14,
underlying 5.19(i), with balance 5.11 proved in the imported conditional leaf.
Only the existing universal 5.3 criterion remains explicit here.
-/

public section
open Subgroup Theory.GroupTheory

namespace FixedPoints
universe u v w
variable {G : Type u} {H : Type w} {A : Type v} [Group G] [Group H] [Group A]
    [Finite G] [Finite A]
    [MulDistribMulAction A G] [MulDistribMulAction A H]

/-- Equivariant surjections map the fixed two-star core into the target fixed core. -/
theorem map_twoStarCore_of_surjective_of_extension
    (hext : Theory.GroupTheory.SylowBoundExtensionCriterion.{max u v} (p := 2))
    (hA : IsPGroup 2 A) (f : G →* H) (hf : Function.Surjective f)
    (he : ∀ (a : A) (x : G), f (a • x) = a • f x) :
    (pStarCore 2 (fixedPointSubgroup A G)).map (mapHom f he) ≤
      pStarCore 2 (fixedPointSubgroup A H) := by
  let D := (fixedPointSubgroup A H).comap f
  have hd (a : A) (x : G) (hx : x ∈ D) : f (a • x) = f x := by
    rw [he]
    exact hx a
  let : IsInvariant A G D := ⟨fun a x => by
    constructor
    · intro hx
      change f (a • x) ∈ fixedPointSubgroup A H
      rw [hd a x hx]
      exact hx
    · intro hx
      have hh := hd a⁻¹ (a • x) hx
      change f x ∈ fixedPointSubgroup A H
      have hhx : f (a⁻¹ • (a • x)) ∈ fixedPointSubgroup A H := hh.symm ▸ hx
      simpa only [inv_smul_smul] using hhx⟩
  have hCD : fixedPointSubgroup A G ≤ D := by
    intro x hx a
    rw [← he, hx a]
  let e : fixedPointSubgroup A D ≃* fixedPointSubgroup A G :=
    { toFun := fun x => ⟨x.val.val, fun a => congrArg Subtype.val (x.property a)⟩
      invFun := fun x => ⟨⟨x.val, hCD x.property⟩, fun a => Subtype.ext (x.property a)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let g := f.subgroupComap (fixedPointSubgroup A H)
  have hg : Function.Surjective g := f.subgroupComap_surjective_of_surjective _ hf
  have hb := Theory.GroupTheory.PStarAction.map_twoStarCore_fixedPoint_le_of_extension
    (G := D) hext hA
  calc
    (pStarCore 2 (fixedPointSubgroup A G)).map (mapHom f he) =
        ((pStarCore 2 (fixedPointSubgroup A D)).map (fixedPointSubgroup A D).subtype).map g := by
      rw [← map_pStarCore e, map_map, map_map]
      rfl
    _ ≤ (pStarCore 2 D).map g := map_mono hb
    _ ≤ pStarCore 2 (fixedPointSubgroup A H) := map_pStarCore_le_of_surjective g hg


/-- Arbitrary invariant normal quotients, with the literal quotient action and map. -/
theorem map_twoStarCore_quotient_le_of_extension
    (hext : Theory.GroupTheory.SylowBoundExtensionCriterion.{max u v} (p := 2))
    (hA : IsPGroup 2 A) (N : Subgroup G) [N.Normal] (hN : IsInvariant A G N) :
    letI : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
    (pStarCore 2 (fixedPointSubgroup A G)).map (quotientMap N hN) ≤
      pStarCore 2 (fixedPointSubgroup A (G ⧸ N)) := by
  let : MulDistribMulAction A (G ⧸ N) := quotientMulDistribMulAction N hN
  exact map_twoStarCore_of_surjective_of_extension hext hA (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (fun _ _ => rfl)
end FixedPoints
