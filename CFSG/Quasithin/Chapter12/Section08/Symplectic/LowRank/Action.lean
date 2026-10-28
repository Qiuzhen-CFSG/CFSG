module
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Intersection
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Normality

/-!
# The faithful action and the section centralizer for 12.8.11(6)

The binary linear action is induced by the published injective action of
H/ker(ρ) on the literal U/Z(U). Its moved and fixed spaces use that action.
The subgroup Xdot₀ is the actor image centralizing What/V₂hat. We include
pointwise fixation of V₂hat in its construction and prove that this is automatic
for the actual X, using the conjugation evaluation equation. Thus the membership
criterion is equality under the literal linear quotient map, not an abstract
isomorphism or a chosen action on another vector space.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.11(6), printed pp.854–855, PDF pp.871–872.
Nontriviality of this subgroup is a separate, still required group argument.
-/

public section

open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

@[expose] def dotLinearAction (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) :
    Hdot F ρ →* (Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat) where
  toFun x :=
    { (faithfulAction F ρ x).toAdditive with
      map_smul' := ZMod.map_smul (faithfulAction F ρ x).toAdditive.toAddMonoidHom }
  map_one' := by ext; simp [map_one]
  map_mul' x y := by ext; simp [map_mul]

theorem dotLinearAction_injective (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat) :
    Function.Injective (dotLinearAction F ρ) := by
  intro x y h
  apply faithfulAction_injective F ρ
  ext v
  exact congrArg (fun e : Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat =>
    (e (Additive.ofMul v)).toMul) h

private def fixedSection {k A D : Type*} [Field k] [AddCommGroup A] [Module k A]
    [Group D] (φ : D →* (A ≃ₗ[k] A)) (L W : Submodule k A) : Subgroup D where
  carrier := {x | (∀ l ∈ L, φ x l = l) ∧ ∀ w ∈ W, φ x w - w ∈ L}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    constructor
    · intro l hl
      simp only [map_mul, LinearEquiv.mul_apply, hy.1 l hl, hx.1 l hl]
    · intro w hw
      have he := hx.1 _ (hy.2 w hw)
      simp only [map_sub] at he
      have heq : φ (x*y) w - w = (φ y w - w) + (φ x w - w) := by
        simp only [map_mul, LinearEquiv.mul_apply]
        rw [← he]
        abel
      rw [heq]
      exact L.add_mem (hy.2 w hw) (hx.2 w hw)
  inv_mem' := by
    intro x hx
    have hfix : ∀ l ∈ L, φ x⁻¹ l = l := by
      intro l hl
      apply (φ x).injective
      simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply,
        hx.1 l hl]
    refine ⟨hfix, ?_⟩
    intro w hw
    have he := hfix _ (hx.2 w hw)
    simp only [map_sub, map_inv, LinearEquiv.coe_inv,
      LinearEquiv.symm_apply_apply] at he
    have heq : φ x⁻¹ w - w = -(φ x w - w) := by
      simp only [map_inv]
      simpa only [neg_sub, LinearEquiv.coe_inv] using congrArg Neg.neg he
    rw [heq]
    exact L.neg_mem (hx.2 w hw)

/-- The subgroup fixing the line and centralizing the indicated section. -/
def Xdot₀ (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) : Subgroup (Hdot F ρ) :=
  dotImage F ρ (F.X g) ⊓ fixedSection (dotLinearAction F ρ)
    (hatSpace F (F.Vi 2)) (hatSpace F F.W)

theorem Xdot_fixes_line (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) (hg : g ∈ F.Gi 2) :
    ∀ x ∈ dotImage F ρ (F.X g), ∀ l ∈ hatSpace F (F.Vi 2),
      dotLinearAction F ρ x l = l := by
  rintro x ⟨h, hh, rfl⟩ l hl
  obtain ⟨u, hu, he⟩ := (show l.toMul ∈ hatImage F (F.Vi 2) from hl)
  change Additive.ofMul (ρ h l.toMul) = l
  rw [← he, hρ]
  have hc : F.U.normalizerMonoidHom
      ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u = u := by
    apply Subtype.ext
    change (h : G) * u * (h : G)⁻¹ = u
    exact mul_inv_eq_iff_eq_mul.mpr ((F.X_le_plane_centralizer g hg hh) u hu).symm
  rw [hc, he, ofMul_toMul]

/-- The moved subspace of the faithful quotient actor on the literal central quotient. -/
@[expose] def movedSpace (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (x : Hdot F ρ) :
    Submodule (ZMod 2) (Additive F.Uhat) :=
  LinearMap.range ((dotLinearAction F ρ x).toLinearMap - LinearMap.id)

/-- The common fixed space of the actual actor image. -/
@[expose] def XfixedSpace (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) :
    Submodule (ZMod 2) (Additive F.Uhat) :=
  ⨅ x : dotImage F ρ (F.X g),
    LinearMap.ker ((dotLinearAction F ρ x).toLinearMap - LinearMap.id)

theorem mem_XfixedSpace_iff (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) (v : Additive F.Uhat) :
    v ∈ XfixedSpace F ρ g ↔ ∀ x ∈ dotImage F ρ (F.X g), dotLinearAction F ρ x v = v := by
  simp [XfixedSpace, LinearMap.mem_ker, sub_eq_zero]

theorem mem_Xdot₀_iff (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u))
    (g : G) (hg : g ∈ F.Gi 2) (x : Hdot F ρ) :
    x ∈ Xdot₀ F ρ g ↔ x ∈ dotImage F ρ (F.X g) ∧
      ∀ w ∈ hatSpace F F.W,
        (hatSpace F (F.Vi 2)).mkQ (dotLinearAction F ρ x w) =
          (hatSpace F (F.Vi 2)).mkQ w := by
  change (x ∈ dotImage F ρ (F.X g) ∧ _ ∧ _) ↔ _
  constructor
  · rintro ⟨hx, _, hm⟩
    refine ⟨hx, fun w hw => ?_⟩
    exact (Submodule.Quotient.eq _).mpr (hm w hw)
  · rintro ⟨hx, hm⟩
    refine ⟨hx, Xdot_fixes_line F ρ hρ g hg x hx, fun w hw => ?_⟩
    exact (Submodule.Quotient.eq _).mp (hm w hw)

/-- The section centralizer is a subgroup of the actual actor image. -/
theorem Xdot₀_le (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (g : G) :
    Xdot₀ F ρ g ≤ dotImage F ρ (F.X g) := inf_le_left

/-- Membership supplies the source displacement bound on the hyperplane. -/
theorem moved_W_le_line_of_mem_Xdot₀ (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (g : G) {x : Hdot F ρ} (hx : x ∈ Xdot₀ F ρ g) :
    (hatSpace F F.W).map ((dotLinearAction F ρ x).toLinearMap - LinearMap.id) ≤
      hatSpace F (F.Vi 2) := by
  rintro _ ⟨w, hw, rfl⟩
  exact hx.2.2 w hw

/-- Evaluation on a representative of the actual faithful quotient. -/
@[simp] theorem dotLinearAction_mk_apply (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (ρ : F.H →* MulAut F.Uhat)
    (h : F.H) (u : F.Uhat) :
    dotLinearAction F ρ (QuotientGroup.mk' ρ.ker h) (Additive.ofMul u) =
      Additive.ofMul (ρ h u) := rfl

/-- Inverting the actor does not change its moved space. Thus the homomorphic
left action and the source's right-conjugation convention give the same space. -/
theorem movedSpace_inv (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (ρ : F.H →* MulAut F.Uhat) (x : Hdot F ρ) :
    movedSpace F ρ x⁻¹ = movedSpace F ρ x := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    refine ⟨-(dotLinearAction F ρ x⁻¹ u), ?_⟩
    change dotLinearAction F ρ x (-(dotLinearAction F ρ x⁻¹ u)) -
      -(dotLinearAction F ρ x⁻¹ u) = dotLinearAction F ρ x⁻¹ u - u
    simp only [map_neg, map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    abel
  · rintro _ ⟨u, rfl⟩
    refine ⟨-(dotLinearAction F ρ x u), ?_⟩
    change dotLinearAction F ρ x⁻¹ (-(dotLinearAction F ρ x u)) -
      -(dotLinearAction F ρ x u) = dotLinearAction F ρ x u - u
    simp only [map_neg, map_inv, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    abel

/-- The marked line is contained in the marked hyperplane, so the quotient
in the section-centralizer criterion is the source section What/V₂hat. -/
theorem hatSpace_plane_le_W (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsElementaryAbelian 2 F.Uhat] : hatSpace F (F.Vi 2) ≤ hatSpace F F.W := by
  rintro v ⟨u, hu, he⟩
  exact ⟨u, F.seed_le_W (F.le_seed 2 hu), he⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
