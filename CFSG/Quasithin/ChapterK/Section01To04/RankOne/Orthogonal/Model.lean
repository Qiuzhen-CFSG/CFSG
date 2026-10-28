module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv

/-!
# A marked orthogonal model for K.3.1.2

The input is an actual equivalence of the layer with SL₂ of the quadratic
field and a binary intertwiner with its Hermitian action. The already proved
Hermitian isometry gives the literal four-dimensional minus orthogonal space,
not a group-family label. Cardinality gives the binary dimension `4s`.

This interface supplies coordinates for the local calculations; it does not
assert module recognition or classify ambient extensions.
Source: Aschbacher–Smith, K.3.1.2, printed p.454.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterK.RankOne
open Representation Representation.BinaryOffender
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- A genuine group identification and intertwiner for the source layer. -/
structure OrthogonalModel (ρ : Representation (ZMod 2) G V) (L : Subgroup G) where
  groupEquiv : L ≃* Matrix.SpecialLinearGroup (Fin 2) (Field s)
  coordinates : V ≃ₗ[ZMod 2] Space s
  intertwines : ∀ (g : L) (v : V),
    coordinates (ρ (g : G) v) = SL2.BinarySmall.hermitian s (groupEquiv g) (coordinates v)

namespace OrthogonalModel
variable {s} {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (M : OrthogonalModel s ρ L)

/-- The actual embedding of the model group in the original ambient group. -/
def modelEmbedding : Matrix.SpecialLinearGroup (Fin 2) (Field s) →* G :=
  L.subtype.comp M.groupEquiv.symm.toMonoidHom

theorem modelEmbedding_injective : Function.Injective M.modelEmbedding :=
  L.subtype_injective.comp M.groupEquiv.symm.injective

theorem modelEmbedding_intertwines (g : Matrix.SpecialLinearGroup (Fin 2) (Field s))
    (v : V) : M.coordinates (ρ (M.modelEmbedding g) v) =
      SL2.BinarySmall.hermitian s g (M.coordinates v) := by
  simpa [modelEmbedding] using M.intertwines (M.groupEquiv.symm g) v

/-- The marked layer is the literal minus Omega over the field of order `2^s`. -/
def minusGroupEquiv : L ≃*
    ClassicalOrthogonal.Minus.Omega (fixedField s)
      (ClassicalOrthogonal.Minus.Space (fixedField s) 1)
      (ClassicalOrthogonal.Minus.quadraticForm (fixedField s) 2) :=
  M.groupEquiv.trans (sl2EquivMinusOmega s)

/-- Additive coordinates are automatically binary-linear. They retain the
specified quadratic isometry over the fixed field on the Hermitian side. -/
def minusCoordinates : V ≃+ ClassicalOrthogonal.Minus.Space (fixedField s) 1 :=
  M.coordinates.toAddEquiv.trans (hermitianMinusIsometry s).toLinearEquiv.toAddEquiv

theorem minus_intertwines (g : L) (v : V) :
    ClassicalOrthogonal.subgroupNatural
      (ClassicalOrthogonal.Minus.Omega (fixedField s)
        (ClassicalOrthogonal.Minus.Space (fixedField s) 1)
        (ClassicalOrthogonal.Minus.quadraticForm (fixedField s) 2))
      (M.minusGroupEquiv g) (M.minusCoordinates v) =
        M.minusCoordinates (ρ (g : G) v) := by
  change _ = hermitianMinusIsometry s (M.coordinates (ρ (g : G) v))
  rw [M.intertwines]
  exact sl2EquivMinusOmega_intertwines s (M.groupEquiv g) (M.coordinates v)

include M in
/-- The binary dimension follows from the actual field cardinality and
four-dimensional Hermitian coordinates. -/
theorem finrank_eq : Module.finrank (ZMod 2) V = 4 * s := by
  rw [M.coordinates.finrank_eq]
  have hcard := Module.natCard_eq_pow_finrank (K := fixedField s) (V := Space s)
  rw [card_fixedField, finrank_space, ← pow_mul, Nat.mul_comm s 4] at hcard
  have hbin := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space s)
  have he : 2 ^ Module.finrank (ZMod 2) (Space s) = 2 ^ (4 * s) := by
    simpa only [Nat.card_zmod] using hbin.symm.trans hcard
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he

end OrthogonalModel
end CFSG.Quasithin.ChapterK.RankOne
