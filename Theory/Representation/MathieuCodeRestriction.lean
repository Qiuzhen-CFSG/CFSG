module

public import Theory.Representation.MathieuCodeRestriction.FixedSpaces
public import Theory.Representation.MathieuCodeRestriction.AtlasComparison
public import Theory.Mathieu.M23.Properties.PointStabilizer

/-!
# Restricting the Mathieu code and cocode to M₂₃

The embedding is the native Witt-design point stabilizer, extending the
23-point permutation by fixing Atlas point 24 (native point zero). The code
and cocode actions for M₂₃ are the restrictions of the literal M₂₄ quotients.
The predicates for arbitrary groups and modules require both a group
isomorphism and a genuine intertwining linear equivalence. The exports also
include faithfulness and the strict Sylow fixed-space inequality for M₂₄,
and an explicit coordinate comparison with the licensed ATLAS Golay code.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.4.3(3),
printed p.241, and H.13.1, printed p.395.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu
open scoped BigOperators Pointwise

namespace MathieuCode

/-- The actual point-stabilizer embedding, fixing native point 0 (Atlas point 24). -/
def pointEmbedding : M23 →* M24 :=
  m23ExtendHom.codRestrict M24 m23Extend_mem_M24

theorem pointEmbedding_injective : Function.Injective pointEmbedding :=
  fun _ _ h => m23ExtendHom_injective (congrArg Subtype.val h)

theorem pointEmbedding_apply (g : M23) (i : Fin 23) :
    (pointEmbedding g : Equiv.Perm (Fin 24)) (m23PointEmbedding i) =
      m23PointEmbedding ((g : Equiv.Perm (Fin 23)) i) :=
  m23ExtendHom_apply_embedded g i

theorem pointEmbedding_fixed (g : M23) :
    (pointEmbedding g : Equiv.Perm (Fin 24)) 0 = 0 := m23ExtendHom_apply_24 g

/-- The image is exactly the native point stabilizer, not merely an abstract copy. -/
theorem pointEmbedding_range :
    pointEmbedding.range = MulAction.stabilizer M24 (0 : Fin 24) := by
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨g, rfl⟩
    exact pointEmbedding_fixed g
  · have hs := Nat.card_congr m23EquivM24PointStabilizer.toEquiv
    have hr := Nat.card_congr (MonoidHom.ofInjective pointEmbedding_injective).toEquiv
    exact le_of_eq (hs.symm.trans hr)

/-- The eleven-dimensional code restricted along the point-stabilizer embedding. -/
def m23CodeRepresentation : Representation (ZMod 2) M23 Code :=
  codeRepresentation.comp pointEmbedding

/-- The eleven-dimensional cocode restricted along the point-stabilizer embedding. -/
def m23CocodeRepresentation : Representation (ZMod 2) M23 Cocode :=
  cocodeRepresentation.comp pointEmbedding

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- An actual M₂₃ code module, up to group isomorphism and an intertwining linear equivalence. -/
def IsM23Code (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ e : G ≃* M23, ∃ E : V ≃ₗ[ZMod 2] Code,
    ∀ g v, E (ρ g v) = m23CodeRepresentation (e g) (E v)

/-- An actual M₂₃ cocode module, up to group isomorphism and an intertwining linear equivalence. -/
def IsM23Cocode (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ e : G ≃* M23, ∃ E : V ≃ₗ[ZMod 2] Cocode,
    ∀ g v, E (ρ g v) = m23CocodeRepresentation (e g) (E v)

theorem isM23Code : IsM23Code m23CodeRepresentation :=
  ⟨MulEquiv.refl M23, LinearEquiv.refl (ZMod 2) Code, fun _ _ => rfl⟩

theorem isM23Cocode : IsM23Cocode m23CocodeRepresentation :=
  ⟨MulEquiv.refl M23, LinearEquiv.refl (ZMod 2) Cocode, fun _ _ => rfl⟩

end MathieuCode
