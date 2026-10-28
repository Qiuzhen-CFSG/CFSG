module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits.Six

/-!
# The square conjugator in the actual marked parabolic

The action is conjugation on the ambient elementary abelian V. Its actual
image is identified, equivariantly, with the six-letter plane parabolic in
A₆ or S₆. This records the source L₂T marking, including the plane V₂ and the
vector generating V₁. The explicit even involutions from `Six` lift through
that image equivalence. Their squares act trivially on V and hence centralize
z. An order-two subgroup A ≤ V₂ is consequently V₁^l for such an l in L₂T.

The explicit earlier inputs are the natural V identification and vanishing
C_V(L) from 13.5.2(3), the marked flag and M₂=L₂T from Notation 13.2.1 with
T Sylow, and H=G₁=C_G(z). The `L2` of `BinaryFlags` is a full alternating
stabilizer: the model identifies the image of source L₂T, not its two-residual.
No square or orbit witness is an input.

Source: Aschbacher–Smith, 13.8.7, printed p.949, sufficiency of (*).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
open Theory.SpecificGroups.SymmetricSix
open BinaryFlags.NaturalGeometry BinaryPermutation
variable {G : Type*} [Group G]

/-- The actual L₂T-action, with its marked six-letter parabolic and plane. -/
structure MarkedPlaneAction (L₂ T V V₂ : Subgroup G) [IsElementaryAbelian 2 V] where
  plane_le : V₂ ≤ V
  normalizes : L₂ ⊔ T ≤ normalizer (V : Set G)
  action : ↥(L₂ ⊔ T) →* MulAut V
  apply_val : ∀ l : ↥(L₂ ⊔ T), ∀ v : V,
    (action l v : G) = (l : G) * (v : G) * (l : G)⁻¹
  parabolic : Subgroup (Equiv.Perm (Fin 6))
  parabolic_eq : parabolic = BinaryFlags.L2 ∨ parabolic = BinaryFlags.H2
  groupEquiv : action.range ≃* parabolic
  moduleEquiv : Additive V ≃ₗ[ZMod 2] natural (Fin 6)
  intertwines : ∀ a : action.range, ∀ v : V,
    moduleEquiv (Additive.ofMul (a.val v)) =
      naturalRepresentation _ (groupEquiv a).val (moduleEquiv (Additive.ofMul v))
  plane_marking : ∀ v : V,
    (v : G) ∈ V₂ ↔ moduleEquiv (Additive.ofMul v) ∈ canonicalPlane

namespace MarkedPlaneAction
variable {L₂ T V V₂ : Subgroup G} [IsElementaryAbelian 2 V]

/-- Lift an explicit involution in the marked parabolic. Its square fixes the
original generator, hence lies in its actual ambient centralizer. -/
theorem square_conjugator (P : MarkedPlaneAction L₂ T V V₂)
    (H A : Subgroup G) (z : V)
    (hH : H = centralizer ({(z : G)} : Set G))
    (hz : P.moduleEquiv (Additive.ofMul z) = pairVector 4 5)
    (hA : A ≤ V₂) (hcard : Nat.card A = 2) :
    ∃ l ∈ L₂ ⊔ T, A = (zpowers (z : G)).conjBy l ∧ l ^ 2 ∈ H := by
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  have ha1 : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  let av : V := ⟨a, P.plane_le (hA a.property)⟩
  have han : P.moduleEquiv (Additive.ofMul av) ≠ 0 := by
    intro he
    have hh := P.moduleEquiv.injective (he.trans (map_zero _).symm)
    exact ha1 (congrArg Subtype.val hh)
  obtain ⟨s, hs, hs2, hsa⟩ := SixCenterGeometry.square_swap
    (P.moduleEquiv (Additive.ofMul av))
    ((P.plane_marking av).mp (hA a.property)) han
  have hsp : s ∈ P.parabolic := by
    rcases P.parabolic_eq with hp | hp
    · rwa [hp]
    · rw [hp]
      exact hs.1
  let actor : P.action.range := P.groupEquiv.symm ⟨s, hsp⟩
  obtain ⟨l, hl⟩ := actor.property
  have hal : (⟨P.action l, ⟨l, rfl⟩⟩ : P.action.range) = actor := Subtype.ext hl
  have hmodel : P.groupEquiv ⟨P.action l, ⟨l, rfl⟩⟩ = ⟨s, hsp⟩ := by
    rw [hal]
    exact P.groupEquiv.apply_symm_apply _
  have hlz : P.action l z = av := by
    have he := P.intertwines ⟨P.action l, ⟨l, rfl⟩⟩ z
    rw [hmodel, hz] at he
    exact P.moduleEquiv.injective (he.trans hsa)
  have hal2 : actor ^ 2 = 1 := by
    apply P.groupEquiv.injective
    rw [map_pow, map_one]
    change (P.groupEquiv (P.groupEquiv.symm ⟨s, hsp⟩)) ^ 2 = 1
    rw [P.groupEquiv.apply_symm_apply]
    exact Subtype.ext hs2
  have hl2 : P.action (l ^ 2) = 1 := by
    rw [map_pow, hl]
    exact congrArg Subtype.val hal2
  refine ⟨l, l.property, ?_, ?_⟩
  · rw [CenterQuotientAction.line_eq_zpowers A hcard a ha1]
    change zpowers (a : G) = (zpowers (z : G)).map (MulAut.conj (l : G)).toMonoidHom
    rw [MonoidHom.map_zpowers]
    congr 1
    exact (P.apply_val l z).symm.trans (congrArg Subtype.val hlz) |>.symm
  · rw [hH]
    apply mem_centralizer_singleton_iff.mpr
    apply (mul_inv_eq_iff_eq_mul).mp
    have he := P.apply_val (l ^ 2) z
    rw [hl2] at he
    exact he.symm

end MarkedPlaneAction
end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair

end
