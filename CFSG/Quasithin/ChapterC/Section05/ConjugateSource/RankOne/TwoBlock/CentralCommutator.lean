module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Setup

/-!
# A pointwise commutator cannot lie in the central cover kernel

If [u,s] belongs to C_U(K), the image of u is fixed by s on the natural
quotient. The genuine fixed-vector lifting theorem makes u itself fixed.
This is the precise I.2.3.1 input at the end of C.5.6(7); no assertion that
the whole central layer vanishes is made.

Source: Aschbacher–Smith, C.5.6(7), printed p.160.
-/
public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.central_commutator_eq_one (h : Setup R K F)
    {u s : G} (hu : u ∈ U K) (hs : s ∈ S R)
    (hc : ⁅u,s⁆ ∈ centralizer (K : Set G)) : ⁅u,s⁆ = 1 := by
  let u₀ : U K := ⟨u,hu⟩
  let s₀ : S R := ⟨s,hs⟩
  have hk : h.coordinates.projection
      (moduleConjugate h.coordinates.normalizes s₀ u₀ / u₀) = 1 := by
    apply (h.coordinates.projection_kernel _).mpr
    change s*u*s⁻¹/u ∈ centralizer (K : Set G)
    have he : s*u*s⁻¹/u = ⁅u,s⁆⁻¹ := by simp [commutatorElement_def,div_eq_mul_inv,mul_assoc]
    rw [he]
    exact (centralizer (K : Set G)).inv_mem hc
  rw [map_div,div_eq_one] at hk
  have he := congrArg Subtype.val (h.fixedLift s₀ u₀ hk)
  change s*u*s⁻¹=u at he
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_inv_eq_iff_eq_mul.mp he).symm
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
