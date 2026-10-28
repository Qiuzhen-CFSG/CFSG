module

public import Theory.Representation.PSL3Two.TransvectionFixed
public import Theory.Representation.PSL3Two.TransvectionFixedLift.Generators
public import Theory.Representation.BinaryNaturalDual
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution
import Mathlib.Tactic.FinCases

/-!
# The quadratic inverse image of a transvection fixed space

Let an extraspecial two-group map onto the binary natural three-space plus its
literal linear dual, with central kernel and square-one elements exactly over
the zeros of the evaluation quadratic form. The inverse image of a nonidentity
involution's fixed space is isomorphic to E₄ × D₈.

For I + E₀₂, lift (e₀,0), (0,e₂*), (e₁,0), and (0,e₁*). Their quadratic values
make them involutions. The first two commute with all four; the last two have
a product of order four. Projection onto the radical coordinates separates
the elementary factor from the dihedral subgroup. Multiplication is injective,
and the fixed-space and kernel counts make it surjective. The literal natural
and contragredient action preserves evaluation and transports this construction
to every nonidentity involution.

Source motivation: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.58 and the first paragraph proving 15.3.61(2), printed pp.1148–1150.
This structural result keeps square compatibility explicit; its source-theorem
consumer must establish that premise for its chosen coordinates.
-/

public section

open Matrix BinaryLinearThree
namespace BinaryLinearThree.TransvectionFixedLift
open TransvectionFixed
private abbrev τ := FourGroupGeometry.FixedSpaces.involution
private def point : Fin 4 → Space := ![
  (![1,0,0], 0),
  (0, LinearMap.proj 2),
  (![0,1,0], 0),
  (0, LinearMap.proj 1)]

private theorem point_fixed (i : Fin 4) : action τ (point i) = point i := by
  have hi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right (by decide)
  apply Prod.ext
  · fin_cases i <;> decide
  · apply LinearMap.ext
    intro v
    change (point i).2 (τ⁻¹.val *ᵥ v) = (point i).2 v
    rw [hi]
    fin_cases i <;>
      simp [point, τ, FourGroupGeometry.FixedSpaces.involution,
        dotProduct, Fin.sum_univ_three]

private theorem point_quadratic (i : Fin 4) : BinaryNaturalDual.quadratic (point i) = 0 := by
  fin_cases i <;> rfl

private theorem point_sum_quadratic (i j : Fin 4) (h : i < 2 ∨ j < 2) :
    BinaryNaturalDual.quadratic (point i + point j) = 0 := by
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [Fin.lt_def] at h)

private theorem point_two_three_quadratic :
    BinaryNaturalDual.quadratic (point 2 + point 3) = 1 := rfl

private def radicalProjection : Space →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun w := ![w.1 0, w.2 ![0,0,1]]
  map_add' u v := by ext i; fin_cases i <;> simp
  map_smul' c v := by ext i; fin_cases i <;> simp

private theorem radicalProjection_point : ∀ i : Fin 4,
    radicalProjection (point i) = ![![1,0], ![0,1], 0, 0] i := by
  intro i
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

private theorem quadratic_action (k : Group) (w : Space) :
    BinaryNaturalDual.quadratic (action k w) = BinaryNaturalDual.quadratic w := by
  change w.2 (W k⁻¹ (W k w.1)) = w.2 w.1
  rw [W.inv_self_apply]

private theorem fixed_conjugator (g k : Group) (hk : g * k = k * τ) (w : Space) :
    action τ (action k⁻¹ w) = action k⁻¹ w ↔ action g w = w := by
  have he : action g w = action k (action τ (action k⁻¹ w)) := by
    calc
      action g w = action g (action k (action k⁻¹ w)) := by rw [action.self_inv_apply]
      _ = action k (action τ (action k⁻¹ w)) := by
        rw [← Module.End.mul_apply, ← map_mul, hk, map_mul, Module.End.mul_apply]
  constructor
  · intro h
    rw [he, h, action.self_inv_apply]
  · intro h
    apply (action.apply_bijective k).injective
    rw [← he, h, action.self_inv_apply]

private theorem commute_of_squares {H : Type*} [_root_.Group H] (x y : H)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) : Commute x y := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy)
  have hxyi : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right
    (by simpa only [pow_two] using hxy)
  change x * y = y * x
  simpa only [_root_.mul_inv_rev, hxi, hyi] using hxyi.symm

private theorem card_preimage {G K : Type*} [_root_.Group G] [_root_.Group K]
    (f : G →* K) (hf : Function.Surjective f) (s : Set K) :
    Nat.card {x : G // f x ∈ s} = Nat.card f.ker * Nat.card s := by
  classical
  let lift : K → G := fun x => (hf x).choose
  have hl (x : K) : f (lift x) = x := (hf x).choose_spec
  let e : {x : G // f x ∈ s} ≃ f.ker × s :=
    { toFun := fun x => (⟨x.val * (lift (f x.val))⁻¹, by simp [hl]⟩, ⟨f x.val, x.property⟩)
      invFun := fun x => ⟨x.1.val * lift x.2.val, by simp [hl, MonoidHom.mem_ker.mp x.1.property]⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by
        rintro ⟨x,y⟩
        apply Prod.ext
        · apply Subtype.ext
          simp [hl, MonoidHom.mem_ker.mp x.property]
        · apply Subtype.ext
          simp [hl, MonoidHom.mem_ker.mp x.property] }
  rw [Nat.card_congr e, Nat.card_prod]

private theorem standard_preimage {Q : Type*} [_root_.Group Q] [Finite Q] [IsExtraspecial 2 Q]
    (f : Q →* Multiplicative Space) (hf : Function.Surjective f)
    (hker : f.ker = Subgroup.center Q)
    (hquad : ∀ x : Q, x ^ 2 = 1 ↔ BinaryNaturalDual.quadratic (f x).toAdd = 0) :
    Nonempty ((fixedSubgroup τ).comap f ≃* (E × DihedralGroup 4)) := by
  classical
  let H := (fixedSubgroup τ).comap f
  have hfixed : Nat.card (fixedSubgroup τ) = 16 := by
    let e : fixedSubgroup τ ≃ Fixed τ :=
      Multiplicative.toAdd.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr e, card_fixed τ (by decide) (by decide)]
  have hcard : Nat.card H = 32 := by
    calc
      Nat.card H = Nat.card f.ker * Nat.card (fixedSubgroup τ) :=
        card_preimage f hf (fixedSubgroup τ : Set (Multiplicative Space))
      _ = 32 := by rw [hker, IsExtraspecial.center_order_p 2 Q, hfixed]
  choose lift hl using fun i : Fin 4 => hf (.ofAdd (point i))
  let x (i : Fin 4) : H := ⟨lift i, by
    change action τ (f (lift i)).toAdd = (f (lift i)).toAdd
    rw [hl]
    exact point_fixed i⟩
  have hx (i : Fin 4) : f (x i : Q) = .ofAdd (point i) := hl i
  have hs (i : Fin 4) : x i ^ 2 = 1 := by
    apply Subtype.ext
    apply (hquad (x i)).mpr
    rw [hx]
    exact point_quadratic i
  have hsum (i j : Fin 4) (h : i < 2 ∨ j < 2) : (x i * x j) ^ 2 = 1 := by
    apply Subtype.ext
    apply (hquad ((x i : Q) * x j)).mpr
    rw [map_mul, hx, hx]
    exact point_sum_quadratic i j h
  have hcomm (i j : Fin 4) (h : i < 2 ∨ j < 2) : Commute (x i) (x j) :=
    commute_of_squares _ _ (hs i) (hs j) (hsum i j h)
  let r : H →* E := radicalProjection.toAddMonoidHom.toMultiplicative.comp
    (f.comp H.subtype)
  have hr (i : Fin 4) : r (x i) = .ofAdd (radicalProjection (point i)) := by
    change Multiplicative.ofAdd (radicalProjection (f (x i : Q)).toAdd) = _
    rw [hx]
    rfl
  apply nonempty_equiv_of_lifts hcard r (x 0) (x 1) (x 2) (x 3)
    (hs 0) (hs 1) (hs 2) (hs 3)
    (hcomm 0 1 (by decide)) (hcomm 0 2 (by decide)) (hcomm 0 3 (by decide))
    (hcomm 1 2 (by decide)) (hcomm 1 3 (by decide))
  · rw [hr, radicalProjection_point]
    rfl
  · rw [hr, radicalProjection_point]
    rfl
  · rw [hr, radicalProjection_point]
    rfl
  · rw [hr, radicalProjection_point]
    rfl
  · intro he
    have hq := (hquad ((x 2 : Q) * x 3)).mp (congrArg Subtype.val he)
    rw [map_mul, hx, hx] at hq
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) (point_two_three_quadratic.symm.trans hq)
  · apply Subtype.ext
    exact IsExtraspecial.pow_four_eq_one _

/-- The inverse image of the fixed space of a binary transvection in an
extraspecial two-group is a binary plane times D₈, provided its square map is
the natural-plus-dual evaluation quadratic form. -/
theorem nonempty_equiv_preimage {Q : Type*} [_root_.Group Q] [Finite Q] [IsExtraspecial 2 Q]
    (f : Q →* Multiplicative Space) (hf : Function.Surjective f)
    (hker : f.ker = Subgroup.center Q)
    (hquad : ∀ x : Q, x ^ 2 = 1 ↔ BinaryNaturalDual.quadratic (f x).toAdd = 0)
    (g : Matrix.PSL3Two.SL) (hg : g ≠ 1) (hsq : g * g = 1) :
    Nonempty ((fixedSubgroup g).comap f ≃*
      (Multiplicative (Fin 2 → ZMod 2) × DihedralGroup 4)) := by
  obtain ⟨k, hk⟩ := FourGroupGeometry.FixedSpaces.exists_involution_conjugator g hg hsq
  let e : Space ≃ₗ[ZMod 2] Space :=
    LinearEquiv.ofBijective (action k⁻¹) (action.apply_bijective k⁻¹)
  let m : Multiplicative Space ≃* Multiplicative Space := e.toAddEquiv.toMultiplicative
  let f' : Q →* Multiplicative Space := m.toMonoidHom.comp f
  have hf' : Function.Surjective f' := m.surjective.comp hf
  have hker' : f'.ker = Subgroup.center Q := by
    rw [← hker]
    ext x
    change m (f x) = 1 ↔ f x = 1
    exact m.map_eq_one_iff
  have hquad' (x : Q) : x ^ 2 = 1 ↔ BinaryNaturalDual.quadratic (f' x).toAdd = 0 := by
    change x ^ 2 = 1 ↔ BinaryNaturalDual.quadratic (action k⁻¹ (f x).toAdd) = 0
    rw [quadratic_action]
    exact hquad x
  have hH : (fixedSubgroup τ).comap f' = (fixedSubgroup g).comap f := by
    ext x
    change action τ (action k⁻¹ (f x).toAdd) = action k⁻¹ (f x).toAdd ↔
      action g (f x).toAdd = (f x).toAdd
    exact fixed_conjugator g k hk (f x).toAdd
  obtain ⟨eH⟩ := standard_preimage f' hf' hker' hquad'
  exact ⟨(MulEquiv.subgroupCongr hH.symm).trans eH⟩

end BinaryLinearThree.TransvectionFixedLift
