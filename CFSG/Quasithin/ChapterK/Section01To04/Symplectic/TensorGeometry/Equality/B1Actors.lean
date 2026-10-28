module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Models
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.B1CommonRoot
public import Theory.Representation.BinaryOffender.GeneratedCore

/-!
# The all-b₁ actor bound in the symplectic tensor case

Transport the elementary actor through the literal component inclusion and
its marked symplectic isomorphism. The common-root theorem places its image
in a conjugate of root 0, whose order is the defining field order. Since the
tensor identification has field order 2^(2s), the original actor has rank at
most 2s. This supplies the all-b₁ branch of the rank argument; it needs no
assumption about tensor fixed spaces or action ratios.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.InvolutionTypes

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- An elementary actor all of whose nonidentity model images have Suzuki
 type b₁ lies in a single root group and has binary rank at most 2s. -/
theorem tensor_b1_actor_rank_le {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s)
    {A : Subgroup G} [IsElementaryAbelian 2 A] (hAL : A ≤ L)
    (hb : ∀ x ∈ (A.subgroupOf L).map h.groupEquiv.toMonoidHom,
      x ≠ 1 → IsB1 x) : rank A ≤ 2 * s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 :=
    charP_of_injective_algebraMap (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  let : IsElementaryAbelian 2 (A.subgroupOf L) := IsElementaryAbelian.subgroupOf hAL
  let B := (A.subgroupOf L).map h.groupEquiv.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hr := SymplecticConjugatePair.elementary_b1_rank_le h.field_card B hb
  dsimp [B] at hr
  rwa [rank_map_injective _ h.groupEquiv.injective, rank_subgroupOf hAL] at hr

end CFSG.Quasithin.ChapterK.Symplectic
