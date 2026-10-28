module

public import Theory.Representation.SL2NaturalOffenders.Ratios
public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.Algebra.CharP.Reduced
/-!
# Pointwise fixers in a semilinear natural SL₂ extension

A two-element acting linearly over the defining field has determinant one and
therefore lies in the marked natural SL₂ layer. For a normal layer, an ambient
Sylow element fixing the layer Sylow's fixed line pointwise has trivial field
automorphism, so the first result applies. The fixed line is obtained from the
sharp natural-module dimension formula, with no coordinate choice or splitting.

Source: Aschbacher–Smith B.2.20 and B.6.10, printed pp.82 and 117.
-/

public section
open Representation Representation.BinaryOffender
namespace Representation.SL2NaturalOffenders
variable {F H : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Group H] [Finite H]
omit [Finite F] [Finite H] in
/-- A linear two-element of a faithful natural extension belongs to SL₂. -/
theorem mem_of_linear_two_power_one (L : Subgroup H)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    {a : H} (ha : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hlin : ∀ (c : F) (v : Fin 2 → F), ρ a (c • v) = c • ρ a v) : a ∈ L := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  let T : Module.End F (Fin 2 → F) :=
    { toFun := ρ a
      map_add' := (ρ a).map_add
      map_smul' := hlin }
  have hpow (n : ℕ) (v : Fin 2 → F) : (T ^ n) v = ρ (a ^ n) v := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ', Module.End.mul_apply, ih, map_mul]
      rfl
  obtain ⟨n, hn⟩ := ha
  have hT : T ^ (2 ^ n) = 1 := by
    apply LinearMap.ext
    intro v
    rw [hpow, hn, map_one]
    rfl
  let M := LinearMap.toMatrix' T
  have hM : M ^ (2 ^ n) = 1 := by
    change (LinearMap.toMatrixAlgEquiv' T) ^ (2 ^ n) = 1
    rw [← map_pow, hT, map_one]
  have hdet : M.det = 1 := by
    have hd : M.det ^ (2 ^ n) = 1 := by
      simpa only [Matrix.det_pow, Matrix.det_one] using congrArg Matrix.det hM
    simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 n 1 M.det).mp (by simpa using hd)
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨M, hdet⟩
  have heq : ρ ((e.symm g : L) : H) = ρ a := by
    apply LinearMap.ext
    intro v
    rw [hnat, e.apply_symm_apply]
    exact LinearMap.toMatrix'_mulVec T v
  exact hfaith heq ▸ (e.symm g).property

/-- An ambient Sylow element fixing the layer Sylow fixed space pointwise lies
in the marked natural layer. -/
theorem mem_layer_of_sylow_fixedSpace (L : Subgroup H) [L.Normal]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : Representation (ZMod 2) H (Fin 2 → F)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v : Fin 2 → F), ρ (g : H) v = Matrix.mulVec (e g).val v)
    (P : Sylow 2 H) {a : H} (ha : a ∈ P)
    (hfix : ∀ v ∈ fixedSpace ρ ((P : Subgroup H) ⊓ L), ρ a v = v) :
    a ∈ L := by
  obtain ⟨Q, hQ⟩ := P.exists_sylow_map_eq_inf_of_normal L
  have hd := Ratios.sylowImage_fixedCodim L e ρ hnat Q
  rw [hQ] at hd
  have hdim := fixedCodim_add_finrank ρ ((P : Subgroup H) ⊓ L)
  have hfull : Module.finrank (ZMod 2) (Fin 2 → F) =
      2 * Module.finrank (ZMod 2) F := by simp [Module.finrank_pi_fintype, two_mul]
  have hp : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  have hpfix : 0 < Module.finrank (ZMod 2) (fixedSpace ρ ((P : Subgroup H) ⊓ L)) := by
    omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpfix
  have hv0 : (v : Fin 2 → F) ≠ 0 := by
    intro hh
    exact hv (Subtype.ext hh)
  have hcv (c : F) : c • (v : Fin 2 → F) ∈ fixedSpace ρ ((P : Subgroup H) ⊓ L) := by
    intro g
    change ρ (g : H) (c • (v : Fin 2 → F)) = c • (v : Fin 2 → F)
    rw [hnat ⟨g, g.property.2⟩, Matrix.mulVec_smul]
    have hh : ρ (g : H) (v : Fin 2 → F) = v := v.property g
    rw [hnat ⟨g, g.property.2⟩] at hh
    rw [hh]
  obtain ⟨σ, hσ⟩ := normalizer_semilinear L e ρ hnat a
  have hs (c : F) : σ c = c := by
    apply smul_left_injective F hv0
    change σ c • (v : Fin 2 → F) = c • (v : Fin 2 → F)
    calc
      σ c • (v : Fin 2 → F) = σ c • ρ a v := by rw [hfix v v.property]
      _ = ρ a (c • (v : Fin 2 → F)) := (hσ c v).symm
      _ = c • (v : Fin 2 → F) := hfix _ (hcv c)
  apply mem_of_linear_two_power_one L e ρ hfaith hnat
  · obtain ⟨n, hn⟩ := (isPGroup_iff_pow_pow_eq_one.mp P.isPGroup') ⟨a, ha⟩
    exact ⟨n, congrArg Subtype.val hn⟩
  · intro c w
    rw [hσ, hs]
end Representation.SL2NaturalOffenders
