module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.LocalGeometry

/-!
# Actual centralizer coordinates for the order-25 field

A frame records a common Sylow subgroup, a nontrivial linear central twist,
and the actual comparison between the two involution centralizers. Such a
frame exists by the quadratic-field descent and odd-index calculation,
including characteristic five. No generation or fusion is asserted here.

The two subgroups used in the subsequent fusion calculation are literal
subgroups of the inner model: the inverse image of the fixed-field PSL₂
layer in the common Sylow, and its intersection with the local derived
group. In the S₅ × C₂ coordinates these will be E₈ and its distinguished
four-group. Their orders and fusion remain separate obligations.

Source: Aschbacher--Smith E.1.14(6), printed p.214, referring to
Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

variable {F : Type*} [Field F] [Finite F]

/-- A common Sylow and its two actual field-involution centralizers.
The comparison is an isomorphism of the literal subgroups. -/
structure Frame (σ : F ≃+* F) where
  T : Sylow 2 (innerModel F σ)
  z : innerModel F σ
  z_order : orderOf z = 2
  z_linear : (z : PGammaL2 F).right = 1
  twist_order : orderOf (z * pure σ) = 2
  left_le : (T : Subgroup (innerModel F σ)) ≤ centralizer ({pure σ} : Set _)
  right_le : (T : Subgroup (innerModel F σ)) ≤ centralizer ({z * pure σ} : Set _)
  comparison : centralizer ({z * pure σ} : Set (innerModel F σ)) ≃*
    centralizer ({pure σ} : Set (innerModel F σ))

/-- The local construction already gives these coordinates at characteristic
five; neither subfield maximality nor a generating-pair hypothesis is needed. -/
theorem nonempty_frame (hF : Nat.card F = 5 ^ 2) (σ : F ≃+* F)
    (hσ : orderOf σ = 2) [Finite (innerModel F σ)] : Nonempty (Frame σ) := by
  obtain ⟨T, z, hz, hzr, hzs, hTC, hTD, _⟩ :=
    CentralizerPair.exists_central_twist (by decide : Nat.Prime 5) (by decide) hF σ hσ
  have hr : ((z * pure σ : innerModel F σ) : PGammaL2 F).right = σ := by
    change (z : PGammaL2 F).right * σ = σ
    rw [hzr, one_mul]
  obtain ⟨e⟩ := CentralizerPair.centralizer_equiv_of_field_involution
    (by decide : Nat.Prime 5) (by decide) hF σ hσ (z * pure σ) hzs hr
  exact ⟨⟨T, z, hz, hzr, hzs, hTC, hTD, e⟩⟩

namespace Frame
variable {σ : F ≃+* F} (c : Frame σ)

/-- `false` denotes the pure involution; `true` denotes its linear twist. -/
@[expose] def involution : Bool → innerModel F σ
  | false => pure σ
  | true => c.z * pure σ

/-- Both coordinates use actual ambient centralizers. -/
@[expose] def centralizerAt (i : Bool) : Subgroup (innerModel F σ) :=
  centralizer ({c.involution i} : Set (innerModel F σ))

/-- The comparison for the pure involution is the identity. -/
@[expose] def comparisonAt : (i : Bool) → c.centralizerAt i ≃*
    centralizer ({pure σ} : Set (innerModel F σ))
  | false => MulEquiv.refl _
  | true => c.comparison

omit [Finite F] in
theorem involution_order (hσ : orderOf σ = 2) (i : Bool) :
    orderOf (c.involution i) = 2 := by
  cases i
  · apply (orderOf_eq_prime_iff (x := c.involution false)).mpr
    have hs := (orderOf_eq_prime_iff (x := σ)).mp hσ
    constructor
    · apply Subtype.ext
      change (SemidirectProduct.inr σ : PGammaL2 F) ^ 2 = 1
      rw [← map_pow, hs.1, map_one]
    · intro h
      apply hs.2
      exact congrArg (fun x : innerModel F σ => (x : PGammaL2 F).right) h
  · exact c.twist_order

omit [Finite F] in
theorem sylow_le (i : Bool) : (c.T : Subgroup (innerModel F σ)) ≤ c.centralizerAt i := by
  cases i
  · exact c.left_le
  · exact c.right_le

/-- The exact projection required by `HasPositionedCentralizerGeometry`. -/
@[expose] def projection (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2) (i : Bool) :
    c.centralizerAt i →* PGL2 (FixedPoints.subfield (zpowers σ) F) :=
  (projectiveProjection hF σ hσ).comp (c.comparisonAt i).toMonoidHom

/-- Position of an original ambient subgroup in one of the two coordinates. -/
@[expose] def IsPositioned (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
    (i : Bool) (A : Subgroup (innerModel F σ)) : Prop :=
  PositionedImage (FixedPoints.subfield (zpowers σ) F)
    ((A.subgroupOf (c.centralizerAt i)).map (c.projection hF hσ i))

/-- The common Sylow intersected with the literal inverse image of PSL₂(5). -/
@[expose] def large (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2) (i : Bool) :
    Subgroup (innerModel F σ) :=
  (c.T : Subgroup (innerModel F σ)) ⊓
    (((ProjectiveSpecialLinearGroup.toPGL (n := Fin 2)
      (R := FixedPoints.subfield (zpowers σ) F)).range.comap
        (c.projection hF hσ i)).map (c.centralizerAt i).subtype)

/-- The distinguished subgroup in the actual local derived group. -/
@[expose] def small (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2) (i : Bool) :
    Subgroup (innerModel F σ) :=
  c.large hF hσ i ⊓ (commutator (c.centralizerAt i)).map (c.centralizerAt i).subtype

theorem small_le_large (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2) (i : Bool) :
    c.small hF hσ i ≤ c.large hF hσ i := inf_le_left

end Frame
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
