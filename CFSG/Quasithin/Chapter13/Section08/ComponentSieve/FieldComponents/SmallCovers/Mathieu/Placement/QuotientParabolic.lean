module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement.HexadLift

/-!
# The literal quotient parabolic

The restriction of K→K/O₂(K)≃M₂₂ identifies X modulo the intersection
with the literal O₂,Z(K) with its native image. For the source overlap J,
we also retain its subgroup image in the actual K₁/O₂,Z(K), and transport
ordinary maximality through the compatible hexad quotient equivalence.
Source placement separately proves that the entire denominator lies in J
and that J lies in K₁, so these are the quotients stated on printed p.956.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section
open Subgroup Sporadic.Mathieu Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement

variable {G : Type*} [Group G]

/-- The restriction kernel is the literal central preimage, intersected with X. -/
theorem markedMap_ker_centralPreimage (K X : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hXK : X ≤ K) :
    (markedMap K X e hXK).ker =
      (centralPreimage (pCore 2 K)).comap (inclusion hXK) := by
  rw [centralPreimage_eq_twoCore K e, markedMap, ← MonoidHom.comap_ker,
    componentMap_ker]

/-- The source quotient has the actual marked subgroup as its model. -/
noncomputable def markedQuotientEquiv (K X : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hXK : X ≤ K) :
    (X ⧸ (centralPreimage (pCore 2 K)).comap (inclusion hXK)) ≃*
      markedImage K X e :=
  (QuotientGroup.quotientMulEquivOfEq
    (markedMap_ker_centralPreimage K X e hXK).symm).trans
    ((QuotientGroup.quotientKerEquivRange (markedMap K X e hXK)).trans
      (MulEquiv.subgroupCongr (markedMap_range K X e hXK)))

@[simp] theorem markedQuotientEquiv_mk (K X : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (hXK : X ≤ K) (x : X) :
    (markedQuotientEquiv K X e hXK (QuotientGroup.mk' _ x) : M22) =
      markedMap K X e hXK x := rfl

/-- The literal denominator, now inside the actual ambient K₁. -/
theorem hexadLift_denominator (K : Subgroup G) (e : (K ⧸ pCore 2 K) ≃* M22)
    (B : Finset (Fin 22)) :
    (centralPreimage (pCore 2 K)).comap (inclusion (hexadLift_le K e B)) =
      ((centralPreimage (pCore 2 K)).map K.subtype).subgroupOf (hexadLift K e B) := by
  ext x
  constructor
  · intro hx
    exact ⟨inclusion (hexadLift_le K e B) x, hx, rfl⟩
  · rintro ⟨k, hk, he⟩
    have he' : k = inclusion (hexadLift_le K e B) x := Subtype.ext he
    change inclusion (hexadLift_le K e B) x ∈ centralPreimage (pCore 2 K)
    rwa [← he']

/-- The actual ambient K₁/O₂,Z(K) in the specified native coordinates. -/
noncomputable def hexadLiftQuotientEquiv (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    (hexadLift K e B ⧸ (centralPreimage (pCore 2 K)).comap
      (inclusion (hexadLift_le K e B))) ≃* MulAction.stabilizer M22 B :=
  (markedQuotientEquiv K (hexadLift K e B) e (hexadLift_le K e B)).trans
    (MulEquiv.subgroupCongr (hexadLift_image K e B))

@[simp] theorem hexadLiftQuotientEquiv_mk (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) (x : hexadLift K e B) :
    (hexadLiftQuotientEquiv K e B (QuotientGroup.mk' _ x) : M22) =
      componentMap K e (inclusion (hexadLift_le K e B) x) := rfl

/-- J's subgroup image inside the literal quotient of the ambient K₁. -/
noncomputable def overlapInLiftQuotient (K M : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    Subgroup (hexadLift K e B ⧸ (centralPreimage (pCore 2 K)).comap
      (inclusion (hexadLift_le K e B))) :=
  ((K ⊓ M).subgroupOf (hexadLift K e B)).map (QuotientGroup.mk' _)

/-- The quotient subgroup and the native parabolic have the same inclusion map. -/
theorem overlapInLiftQuotient_image (K M : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22)) :
    (overlapInLiftQuotient K M e B).map (hexadLiftQuotientEquiv K e B).toMonoidHom =
      (markedImage K (K ⊓ M) e).subgroupOf (MulAction.stabilizer M22 B) := by
  rw [overlapInLiftQuotient, map_map]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨inclusion (hexadLift_le K e B) x, hx, rfl⟩
  · rintro ⟨k, hk, he⟩
    have hmem : k ∈ hexadPreimage K e B := by
      change componentMap K e k ∈ MulAction.stabilizer M22 B
      rw [he]
      exact y.property
    exact ⟨⟨k.val, ⟨k, hmem, rfl⟩⟩, hk, Subtype.ext he⟩

/-- Ordinary maximality in the quotient of the actual ambient K₁. -/
theorem overlapInLiftQuotient_isCoatom (K M : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) (B : Finset (Fin 22))
    (hmax : IsCoatom ((markedImage K (K ⊓ M) e).subgroupOf
      (MulAction.stabilizer M22 B))) : IsCoatom (overlapInLiftQuotient K M e B) := by
  apply ((hexadLiftQuotientEquiv K e B).mapSubgroup.isCoatom_iff _).mp
  change IsCoatom ((overlapInLiftQuotient K M e B).map
    (hexadLiftQuotientEquiv K e B).toMonoidHom)
  rwa [overlapInLiftQuotient_image]

/-- The E₁₆-by-A₆ extension in the literal quotient of the ambient K₁. -/
theorem hexadLiftQuotient_extension (K : Subgroup G)
    (e : (K ⧸ pCore 2 K) ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    AlternatingBySixteen (hexadLift K e B ⧸ (centralPreimage (pCore 2 K)).comap
      (inclusion (hexadLift_le K e B))) 6 :=
  (m22Hexad_extension hB).of_equiv (hexadLiftQuotientEquiv K e B).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu.Placement
