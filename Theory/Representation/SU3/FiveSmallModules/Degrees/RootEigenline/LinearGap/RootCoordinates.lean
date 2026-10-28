module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Contracts
public import Theory.Representation.SU3.FiveSmallModules.Degrees.RootEigenline.Geometry

/-!
# The eight inverse torus multipliers in SU₃(5)

The literal SU root-coordinate map is injective. Its first coordinate is a
surjective additive homomorphism whose kernel is central, and its intrinsic
center maps to the embedded center of the actual SU root subgroup.

Inverse conjugation by torus parameter `k` is the Hermitian coordinate action
at `k⁻¹`. When conjugation is fifth power its first multiplier is `k^9`.
A generator of the order-24 unit group makes the first eight such multipliers
distinct. These are the inverse pullbacks used by the dual-character argument,
not merely element-orbit data.

Sources: Huppert II.10.12; Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap

variable {F : Type*} [Field F] (J : HermitianForm 3 F)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The literal SU root coordinates, without passing to the projective group. -/
noncomputable def coordEquiv : hermitianUnipotentCoord J ≃* specialRoot J hJ :=
  MonoidHom.ofInjective (show Function.Injective (hermitianUnipotentSU J hJ) from by
    intro z w h
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
      (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h))

@[simp] theorem coordEquiv_val (z : hermitianUnipotentCoord J) :
    (coordEquiv J hJ z : J.specialSubgroup) = hermitianUnipotentSU J hJ z := by rfl

def firstCoordinate : hermitianUnipotentCoord J →* Multiplicative F where
  toFun z := Multiplicative.ofAdd z.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem firstCoordinate_ker_le_center :
    (firstCoordinate J).ker ≤ Subgroup.center (hermitianUnipotentCoord J) := by
  intro z hz
  have hzero : z.val.1 = 0 := congrArg Multiplicative.toAdd hz
  apply Subgroup.mem_center_iff.mpr
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.val.1 + z.val.1 = z.val.1 + w.val.1
    exact add_comm _ _
  · change w.val.2 + z.val.2 - w.val.1 * J.conj z.val.1 =
      z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1
    simp [hzero, add_comm]

theorem firstCoordinate_surjective (h2 : (2 : F) ≠ 0) :
    Function.Surjective (firstCoordinate J) := by
  intro x
  refine ⟨⟨(x.toAdd, -(x.toAdd * J.conj x.toAdd) / 2), ?_⟩, ?_⟩
  · dsimp only
    simp only [map_div₀, map_neg, map_mul, map_ofNat]
    rw [J.conj_involutive]
    field_simp [h2]
    ring
  · exact ofAdd_toAdd x

variable [Finite F]

/-- Inverse conjugation by the literal SU torus on the coordinate group. -/
noncomputable def inverseTorus (k : Fˣ) : MulAut (hermitianUnipotentCoord J) :=
  (coordEquiv J hJ).trans
    (((specialRoot J hJ).normalizerMonoidHom
      ⟨hermitianTorusSU J hJ k⁻¹,
        specialTorus_normalizes_root J hJ ⟨k⁻¹, rfl⟩⟩).trans
      (coordEquiv J hJ).symm)

theorem inverseTorus_conjugation (k : Fˣ) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentSU J hJ (inverseTorus J hJ k z) =
      (hermitianTorusSU J hJ k)⁻¹ * hermitianUnipotentSU J hJ z *
        hermitianTorusSU J hJ k := by
  have he := congrArg (fun x : specialRoot J hJ => (x : J.specialSubgroup))
    ((coordEquiv J hJ).apply_symm_apply
      ((specialRoot J hJ).normalizerMonoidHom
        ⟨hermitianTorusSU J hJ k⁻¹,
          specialTorus_normalizes_root J hJ ⟨k⁻¹, rfl⟩⟩ (coordEquiv J hJ z)))
  change hermitianUnipotentSU J hJ (inverseTorus J hJ k z) = hermitianTorusSU J hJ k⁻¹ * hermitianUnipotentSU J hJ z *
    (hermitianTorusSU J hJ k⁻¹)⁻¹ at he
  simpa only [map_inv, inv_inv] using he

theorem inverseTorus_eq_action (k : Fˣ) (z : hermitianUnipotentCoord J) :
    inverseTorus J hJ k z = hermitianTorusAction J k⁻¹ z := by
  apply (coordEquiv J hJ).injective
  apply Subtype.ext
  rw [coordEquiv_val, coordEquiv_val, inverseTorus_conjugation]
  apply Subtype.ext
  have he := hermitianTorusGL_mul_unipotent J k⁻¹ z
  change (hermitianTorusGL J k)⁻¹ * hermitianUnipotentGL J z *
      hermitianTorusGL J k = hermitianUnipotentGL J (hermitianTorusAction J k⁻¹ z)
  have hi : hermitianTorusGL J k⁻¹ = (hermitianTorusGL J k)⁻¹ :=
    congrArg Subtype.val (map_inv (hermitianTorusSU J hJ) k)
  rw [hi] at he
  rw [he]
  group

theorem firstCoordinate_inverseTorus (hconj : ∀ x, J.conj x = x ^ 5)
    (k : Fˣ) (z : hermitianUnipotentCoord J) :
    firstCoordinate J (inverseTorus J hJ k z) =
      Multiplicative.ofAdd ((k : F) ^ 9 * (firstCoordinate J z).toAdd) := by
  rw [inverseTorus_eq_action]
  change Multiplicative.ofAdd ((hermitianTorusAction J k⁻¹ z).val.1) = _
  rw [hermitianTorusAction_fst, hconj]
  simp only [Units.val_inv_eq_inv_val, inv_pow, inv_inv]
  congr 1
  change z.val.1 * (k : F)⁻¹ * ((k : F) ^ 5) ^ 2 = (k : F) ^ 9 * z.val.1
  field_simp

omit [Finite F] in
theorem center_invariants_eq {E U : Type*} [Field E] [AddCommGroup U] [Module E U]
    (τ : Representation E J.specialSubgroup U) :
    invariants ((τ.comp (hermitianUnipotentSU J hJ)).comp
      (Subgroup.center (hermitianUnipotentCoord J)).subtype) =
    invariants (τ.comp ((Subgroup.center (specialRoot J hJ)).map
      (specialRoot J hJ).subtype).subtype) := by
  ext v
  constructor
  · intro hv z
    obtain ⟨p, hp, he⟩ := z.property
    obtain ⟨c, hc⟩ := (Subgroup.centerCongr (coordEquiv J hJ)).surjective ⟨p, hp⟩
    have hh := hv c
    have hh' := congrArg (fun x : Subgroup.center (specialRoot J hJ) =>
      (x.val : J.specialSubgroup)) hc
    change hermitianUnipotentSU J hJ c.val = p.val at hh'
    change τ z.val v = v
    rw [← he]
    change τ p.val v = v
    rw [← hh']
    exact hh
  · intro hv z
    exact hv ⟨hermitianUnipotentSU J hJ z.val,
      ⟨coordEquiv J hJ z.val, (Subgroup.centerCongr (coordEquiv J hJ) z).property, rfl⟩⟩

/-- The inverse-pullback multipliers of eight torus powers are distinct. -/
theorem exists_eight_torus_powers (hc : Nat.card F = 5 ^ 2) :
    ∃ k : Fˣ, Function.Injective (fun i : Fin 8 => ((k ^ i.val : Fˣ) : F) ^ 9) := by
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ho : orderOf k = 24 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hk, Nat.card_units, hc]
    norm_num
  have ho9 : orderOf (k ^ 9) = 8 := by
    rw [orderOf_pow, ho]
    norm_num
  refine ⟨k, ?_⟩
  intro i j hij
  apply Fin.ext
  apply pow_injOn_Iio_orderOf (x := k ^ 9)
  · simpa only [Set.mem_Iio, ho9] using i.isLt
  · simpa only [Set.mem_Iio, ho9] using j.isLt
  · apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, pow_right_comm] using hij

end Representation.SU3.FiveSmallModules.Degrees.RootEigenline.LinearGap
