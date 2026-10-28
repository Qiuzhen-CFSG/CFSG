module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.ThreePart

/-!
# Lifting a chosen native hexad subgroup

The inverse image of a native hexad stabilizer defines an actual subgroup
K₁ of K. Its quotient by the literal central preimage O₂,Z(K) is the
native hexad stabilizer, hence is E₁₆-by-A₆. The restriction map, kernel,
and formula on representatives are retained. Choosing the hexad so that
K∩M is its parabolic is a separate placement obligation.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement

variable {G : Type*} [Group G]

/-- K₁ before its inclusion in the ambient group. -/
noncomputable def hexadPreimage (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : Subgroup K :=
  (MulAction.stabilizer M22 B).comap (componentMap K e)

/-- The actual ambient subgroup K₁. -/
noncomputable def hexadLift (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : Subgroup G := (hexadPreimage K e B).map K.subtype

theorem hexadLift_le (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : hexadLift K e B ≤ K := map_subtype_le _

/-- Taking the subgroup of K recovers exactly the original inverse image. -/
theorem hexadLift_subgroupOf (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : (hexadLift K e B).subgroupOf K = hexadPreimage K e B :=
  comap_map_eq_self_of_injective K.subtype_injective _

/-- The actual ambient K₁ maps onto the chosen native stabilizer. -/
theorem hexadLift_image (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : markedImage K (hexadLift K e B) e =
      MulAction.stabilizer M22 B := by
  rw [markedImage, hexadLift_subgroupOf, hexadPreimage]
  exact map_comap_eq_self_of_surjective (componentMap_surjective K e) _

/-- The two presentations of K₁ are identified by the original inclusion in G. -/
noncomputable def hexadLiftEquiv (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : hexadPreimage K e B ≃* hexadLift K e B :=
  (hexadPreimage K e B).equivMapOfInjective K.subtype K.subtype_injective

@[simp] theorem hexadLiftEquiv_apply (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) (x : hexadPreimage K e B) :
    (hexadLiftEquiv K e B x : G) = x.val.val := rfl

/-- Even before choosing a hexad, the entire literal denominator lies in its preimage. -/
theorem centralPreimage_le_hexadPreimage (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    centralPreimage (pCore 2 K) ≤ hexadPreimage K e B := by
  rw [centralPreimage_eq_twoCore K e, ← componentMap_ker K e]
  intro k hk
  change componentMap K e k ∈ MulAction.stabilizer M22 B
  rw [show componentMap K e k = 1 from hk]
  exact one_mem _

/-- Restriction to the actual preimage, with target the native stabilizer. -/
noncomputable def hexadRestriction (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) : hexadPreimage K e B →* MulAction.stabilizer M22 B :=
  (componentMap K e).subgroupComap (MulAction.stabilizer M22 B)

theorem hexadRestriction_surjective (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    Function.Surjective (hexadRestriction K e B) :=
  (componentMap K e).subgroupComap_surjective_of_surjective _ (componentMap_surjective K e)

/-- The restriction kernel is the literal O₂,Z(K) inside K₁. -/
theorem hexadRestriction_ker (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    (hexadRestriction K e B).ker =
      (centralPreimage (pCore 2 K)).subgroupOf (hexadPreimage K e B) := by
  rw [centralPreimage_eq_twoCore K e, ← componentMap_ker K e]
  ext x
  change (⟨componentMap K e x.val, x.property⟩ : MulAction.stabilizer M22 B) = 1 ↔
    componentMap K e x.val = 1
  exact Subtype.ext_iff

/-- The actual quotient, retaining the central-preimage denominator. -/
noncomputable def hexadQuotientEquiv (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    (hexadPreimage K e B ⧸
      (centralPreimage (pCore 2 K)).subgroupOf (hexadPreimage K e B)) ≃*
        MulAction.stabilizer M22 B :=
  (QuotientGroup.quotientMulEquivOfEq (hexadRestriction_ker K e B).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (hexadRestriction K e B)
      (hexadRestriction_surjective K e B))

/-- Formula on representatives for the actual quotient coordinates. -/
@[simp] theorem hexadQuotientEquiv_mk (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) (x : hexadPreimage K e B) :
    hexadQuotientEquiv K e B (QuotientGroup.mk' _ x) = hexadRestriction K e B x := rfl

/-- The genuine extension shape of K₁/O₂,Z(K). -/
theorem hexadQuotient_extension (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    AlternatingBySixteen (hexadPreimage K e B ⧸
      (centralPreimage (pCore 2 K)).subgroupOf (hexadPreimage K e B)) 6 :=
  (m22Hexad_extension hB).of_equiv (hexadQuotientEquiv K e B).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
