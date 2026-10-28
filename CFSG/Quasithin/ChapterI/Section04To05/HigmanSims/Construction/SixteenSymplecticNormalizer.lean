module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenPointPolarity
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenPointTransvections
public import Theory.Representation.BinaryPolarity.TransvectionSurjectivity

/-!
# The actual marked symplectic normalizer quotient

The invariant alternating form has the literal point-core intersections
as its hyperplanes. The original central-four elements act as its fifteen
transvections. Their structural generation identifies the whole faithful
normalizer image with Sp₄(2), preserving its action on the original sixteen.
Self-centralization identifies the kernel with the original sixteen itself,
so the equivalence is defined on the actual quotient N_G(A)/A.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- The literal normalizer quotient of the original pure sixteen is the
full symplectic group, with the actual natural action retained in the marking. -/
theorem TypeAt.sixteen_symplectic_normalizer (h : TypeAt z V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16)
    (hCA : centralizer (A : Set G) = A)
    (hpure : ∀ x ∈ A, x ≠ 1 → IsConj x z)
    (hpoints : ∀ x ∈ A, x ≠ 1 →
      Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) :
    ∃ B : LinearMap.BilinForm (ZMod 2) (Additive A), B.IsAlt ∧ B.Nondegenerate ∧
      (∀ (x : A) (_hx : x ≠ 1) (y : A),
        B (Additive.ofMul x) (Additive.ofMul y) = 0 ↔
          (y : G) ∈ (involutionCentralizer (x : G)).pCoreIn 2) ∧
      ∃ e : B.IsometryEquiv (Matrix.PSp4Three.form (n := 2) (F := ZMod 2)),
        ∃ φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
            Matrix.PSp4Three.Sp 2 (ZMod 2),
          ∀ (g : normalizer (A : Set G)) (x : A),
            (φ (QuotientGroup.mk g)).val *ᵥ (e (Additive.ofMul x)) =
              e (Additive.ofMul (A.normalizerMonoidHom g x)) := by
  obtain ⟨B, hAlt, hN, hInv, hker⟩ := h.sixteen_point_core_form A hA hpure hpoints
  let f := A.normalizerMonoidHom
  let R := f.range
  let ρ := Representation.elementaryRepresentation (p := 2) R.subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact congrArg Additive.toMul (congrArg (fun F => F (Additive.ofMul x)) hab)
  have hd : Module.finrank (ZMod 2) (Additive A) = 2 * 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    rw [Nat.card_zmod] at hc
    exact hc.symm.trans hA
  have hB : ∀ a x y, B (ρ a x) (ρ a y) = B x y := by
    rintro ⟨_, g, rfl⟩ x y
    exact hInv g x.toMul y.toMul
  have ht : ∀ v : Additive A, v ≠ 0 →
      ∃ a : R, ∀ w : Additive A, ρ a w = w + (B w v) • v := by
    intro v hv
    have hv1 : (v.toMul : G) ≠ 1 := fun he => hv (Subtype.ext he)
    obtain ⟨c, _, _, _, hcN, _, hfix, hout⟩ :=
      h.sixteen_point_transvection A hA hCA hpure hpoints v.toMul v.toMul.property hv1
    let g : normalizer (A : Set G) := ⟨c, hcN⟩
    refine ⟨⟨f g, ⟨g, rfl⟩⟩, ?_⟩
    intro w
    have hswap : B w v = B v w := by
      have hh := hAlt.neg_eq w v
      rwa [CharTwo.neg_eq] at hh
    have hzero : B w v = 0 ↔
        (w.toMul : G) ∈ (involutionCentralizer (v.toMul : G)).pCoreIn 2 := by
      rw [hswap]
      exact hker v.toMul hv w.toMul
    by_cases hw : B w v = 0
    · rw [hw, zero_smul, add_zero]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact hfix w.toMul ⟨w.toMul.property, hzero.mp hw⟩
    · have hw1 : B w v = 1 := by
        have hh := (by decide +kernel : ∀ a : ZMod 2, a = 0 ∨ a = 1) (B w v)
        exact hh.resolve_left hw
      rw [hw1, one_smul]
      apply Additive.toMul.injective
      apply Subtype.ext
      exact (hout w.toMul w.toMul.property (fun hh => hw (hzero.mpr hh))).trans
        (setLike_mul_comm v.toMul.property w.toMul.property)
  obtain ⟨e, ψ, hψ⟩ := BinaryPolarity.exists_marked_symplectic_equiv_of_transvections
    2 ρ hρ hd B hAlt hN hB ht
  have hk : f.ker = A.subgroupOf (normalizer (A : Set G)) := by
    change A.normalizerMonoidHom.ker = _
    rw [normalizerMonoidHom_ker, hCA]
  let η := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  refine ⟨B, hAlt, hN, hker, e, η.trans ψ, ?_⟩
  intro g x
  have he : η (QuotientGroup.mk g) = f.rangeRestrict g := rfl
  change (ψ (η (QuotientGroup.mk g))).val *ᵥ (e (Additive.ofMul x)) = _
  rw [he, hψ]
  rfl

end CFSG.Quasithin.HigmanSims
