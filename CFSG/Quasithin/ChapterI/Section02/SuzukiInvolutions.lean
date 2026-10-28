module
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.Suzuki
public import Theory.SpecificGroups.Suzuki.InvolutionFusion
public import Theory.ElementaryAbelian.Basic

/-!
# Involutions in the genuine Suzuki central covers

For Sz(8), the checked involutory generator in its universal fourfold cover
has nontrivial quotient image. Involution fusion lifts every quotient
involution; universality transports those lifts and the elementary central
kernel to every finite quasisimple cover. The ordinary Suzuki covers split
by the proved multiplier theorem. No central kernel is discarded.

Source: Aschbacher--Smith I.1.3(5) and I.2.2(4), pp.407, 409--411.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.SuzukiInvolutionLifts
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterI.LieMultipliers.Suzuki
universe u

private theorem exceptional_projection_involution :
    ∃ x : SchurEightCover.E, x ^ 2 = 1 ∧ SchurEightCover.cover.toMonoidHom x ≠ 1 := by
  refine ⟨SchurEightCover.AtlasModel.generatorA, Subtype.ext
    SchurEightCover.AtlasModel.Data.a_sq, ?_⟩
  intro hx
  rw [SchurEightCover.cover_apply_eq_matrix_action,
    SchurEightCover.AtlasModel.BlockComparison.action_generatorA] at hx
  have hh := (SchurEightCover.AtlasModel.MatrixComparison.equiv).map_eq_one_iff.mp hx
  have hh0 := congrArg (fun g : SchurEightCover.AtlasModel.BlockModel.Model =>
    (g : Equiv.Perm (Fin 65)) 0) hh
  norm_num [SchurEightCover.AtlasModel.BlockModel.generatorA,
    SchurEightCover.AtlasModel.BlockModel.a,
    SchurEightCover.AtlasModel.BlockModel.aFun] at hh0

variable {K : Type u} [Group K] [Finite K] [IsQuasisimple K]

private theorem exceptional_cover_laws (q : Covering K (SuzukiMatrixGroup 1)) :
    (∀ x ∈ q.toMonoidHom.ker, x ^ 2 = 1) ∧
      (∀ y : SuzukiMatrixGroup 1, y ^ 2 = 1 → ∃ x : K, x ^ 2 = 1 ∧ q x = y) := by
  obtain ⟨f, hf, _⟩ := exceptional_covering_isUniversal K q
  have hfac : q.toMonoidHom.comp f.toMonoidHom = SchurEightCover.cover.toMonoidHom :=
    congrArg Covering.toMonoidHom hf
  have hfac' (x : SchurEightCover.E) : q (f x) = SchurEightCover.cover.toMonoidHom x :=
    DFunLike.congr_fun hfac x
  constructor
  · intro x hx
    obtain ⟨a, rfl⟩ := f.surjective x
    have ha : a ∈ SchurEightCover.cover.toMonoidHom.ker := (hfac' a).symm.trans hx
    have hp : a ^ 2 = 1 := by
      have he : (⟨a, ha⟩ : SchurEightCover.cover.toMonoidHom.ker) ^ 2 = 1 := by
        apply exceptionalKernelEquiv.injective
        rw [map_pow, map_one]
        apply Prod.ext <;> exact (show ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 by decide +kernel) _
      exact congrArg Subtype.val he
    change f.toMonoidHom a ^ 2 = 1
    rw [← map_pow, hp, map_one]
  · intro y hy
    by_cases he : y = 1
    · exact ⟨1, one_pow 2, by simpa using he.symm⟩
    obtain ⟨a, ha, hqa⟩ := exceptional_projection_involution
    have haord : orderOf (SchurEightCover.cover.toMonoidHom a) = 2 :=
      orderOf_eq_prime (by rw [← map_pow, ha, map_one]) hqa
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (suzuki_involutions_isConj 1 (by decide) _ y haord (orderOf_eq_prime hy he))
    obtain ⟨b, hb⟩ := q.surjective g
    change q b = g at hb
    refine ⟨b * f a * b⁻¹, ?_, ?_⟩
    · calc
        (b * f a * b⁻¹) ^ 2 = b * (f a) ^ 2 * b⁻¹ := by simp [pow_two, mul_assoc]
        _ = 1 := by rw [← map_pow, ha, map_one]; simp
    · change q.toMonoidHom (b * f.toMonoidHom a * b⁻¹) = y
      rw [map_mul, map_mul, map_inv]
      change q b * q (f a) * (q b)⁻¹ = y
      rw [hb, hfac']
      exact hg

theorem cover_laws (n : ℕ) [hn : Fact (0 < n)]
    (q : Covering K (SuzukiMatrixGroup n)) :
    (∀ x ∈ q.toMonoidHom.ker, x ^ 2 = 1) ∧
      (∀ y : SuzukiMatrixGroup n, y ^ 2 = 1 → ∃ x : K, x ^ 2 = 1 ∧ q x = y) := by
  by_cases he : n = 1
  · subst n; exact exceptional_cover_laws q
  obtain ⟨f, hf, _⟩ := ordinary_identity_isUniversal n (by have hh := hn.out; omega) K q
  have hfac (x : SuzukiMatrixGroup n) : q (f x) = x :=
    DFunLike.congr_fun (congrArg Covering.toMonoidHom hf) x
  constructor
  · intro x hx
    obtain ⟨y, rfl⟩ := f.surjective x
    have hy : y = 1 := (hfac y).symm.trans hx
    simp [hy]
  · intro y hy
    exact ⟨f y, by rw [← map_pow, hy, map_one], hfac y⟩

theorem center_elementary_and_involutions_lift (n : ℕ) (hn : 0 < n)
    (e : (K ⧸ center K) ≃* SuzukiMatrixGroup n) :
    IsElementaryAbelian 2 (center K) ∧
      (∀ y : K ⧸ center K, y ^ 2 = 1 →
        ∃ x : K, x ^ 2 = 1 ∧ QuotientGroup.mk' (center K) x = y) := by
  let : Fact (0 < n) := ⟨hn⟩
  let q : Covering K (SuzukiMatrixGroup n) :=
    ⟨e.toMonoidHom.comp (QuotientGroup.mk' (center K)),
      e.surjective.comp (QuotientGroup.mk'_surjective (center K))⟩
  have hk : q.toMonoidHom.ker = center K := by
    ext x
    change e (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  obtain ⟨hpow, hlift⟩ := cover_laws n q
  constructor
  · refine ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_⟩
    intro x
    exact Subtype.ext (hpow x (hk.symm ▸ x.property))
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hlift (e y) (by rw [← map_pow, hy, map_one])
    exact ⟨x, hx, e.injective hxy⟩
end CFSG.Quasithin.ChapterI.SuzukiInvolutionLifts
