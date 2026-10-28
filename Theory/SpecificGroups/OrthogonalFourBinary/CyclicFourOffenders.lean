module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.Coordinates
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.ElementaryAbelian.CyclicKernel
/-!
# Cyclic-four images in the natural binary orthogonal action

The square of an order-four isometry fixes exactly four of the sixteen
vectors. A nontrivial elementary subgroup of a cyclic four-group is that
square subgroup, of rank one. It therefore cannot be an offender on any
module containing the natural orthogonal module as an invariant subspace.
The finite calculation uses the existing 72 isometry coordinates.

Source: Aschbacher–Smith, original 13.2.9, final paragraph, printed p.881.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace OrthogonalFourBinary
open TerminalLines SylowGeometry
set_option synthInstance.maxSize 10000

/-- The defining linear action of the actual isometry group. -/
def naturalRepresentation : Representation (ZMod 2) IsometryGroup Space where
  toFun g := g.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

set_option maxRecDepth 10000 in
private theorem finite_square_fixed : ∀ k : Code,
    (∀ v : Space, eval k (eval k (eval k (eval k v))) = v) →
    (∃ v : Space, eval k (eval k v) ≠ v) →
    Fintype.card {v : Space // eval k (eval k v) = v} = 4 := by
  decide +kernel

/-- Squaring an order-four isometry leaves exactly four fixed vectors. -/
theorem square_fixed_card (g : IsometryGroup) (hg : orderOf g = 4) :
    Nat.card {v : Space // (g ^ 2).val v = v} = 4 := by
  obtain ⟨k,rfl⟩ := codeMap_bijective.surjective g
  change Nat.card {v : Space // candidate k (candidate k v) = v} = 4
  simp_rw [candidate_eval]
  rw [Nat.card_eq_fintype_card]
  apply finite_square_fixed k
  · intro v
    have h4 : codeMap k ^ 4 = 1 := hg ▸ pow_orderOf_eq_one (codeMap k)
    have hv := congrArg (fun a : IsometryGroup => a.val v) h4
    change candidate k (candidate k (candidate k (candidate k v))) = v at hv
    simpa only [candidate_eval] using hv
  · by_contra! hn
    have h2 : codeMap k ^ 2 = 1 := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      change candidate k (candidate k v) = v
      simpa only [candidate_eval] using hn v
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hg] at hd
    norm_num at hd

/-- The unique involution in a cyclic four-group has fixed codimension two. -/
theorem square_fixedCodim (g : IsometryGroup) (hg : orderOf g = 4) :
    fixedCodim naturalRepresentation (zpowers (g ^ 2)) = 2 := by
  have hc : Nat.card (fixedSpace naturalRepresentation (zpowers (g ^ 2))) = 4 := by
    let e : fixedSpace naturalRepresentation (zpowers (g ^ 2)) ≃
        {v : Space // (g ^ 2).val v = v} :=
      (Equiv.refl Space).subtypeEquiv (fun v => mem_fixedSpace_zpowers_iff _ _ _)
    exact (Nat.card_congr e).trans (square_fixed_card g hg)
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace naturalRepresentation (zpowers (g ^ 2)))
  rw [Nat.card_zmod, hc] at hpow
  have hdim : Module.finrank (ZMod 2)
      (fixedSpace naturalRepresentation (zpowers (g ^ 2))) = 2 := by
    have : 2 ^ Module.finrank (ZMod 2)
        (fixedSpace naturalRepresentation (zpowers (g ^ 2))) = 2 ^ 2 := hpow.symm
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) this
  have hd := fixedCodim_add_finrank naturalRepresentation (zpowers (g ^ 2))
  have hSpace : Module.finrank (ZMod 2) Space = 4 := by
    simp [Space, Plane, F]
  omega
end OrthogonalFourBinary

namespace OrthogonalFourBinary.CyclicFour
variable {G : Type*} [Group G] [Finite G]
private theorem square_eq_of_mem (r : G) (hr : orderOf r = 4) {b : G}
    (hb : b ∈ zpowers r) (hb1 : b ≠ 1) (hb2 : b ^ 2 = 1) : b = r ^ 2 := by
  classical
  obtain ⟨n,hn,he⟩ := (Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hb))
  have hn4 : n < 4 := by simpa [hr] using Finset.mem_range.mp hn
  have hdiv : 4 ∣ n * 2 := by
    have hh : r ^ (n*2) = 1 := by rw [pow_mul,he,hb2]
    simpa [hr] using orderOf_dvd_of_pow_eq_one hh
  have hn2 : n = 2 := by
    have hn0 : n ≠ 0 := by intro h; subst n; simp at he; exact hb1 he.symm
    omega
  simpa [hn2] using he.symm

private theorem elementary_eq_square (r : G) (hr : orderOf r = 4)
    (B : Subgroup G) [IsElementaryAbelian 2 B]
    (hB : B ≤ zpowers r) (hne : B ≠ ⊥) : B = zpowers (r ^ 2) := by
  obtain ⟨b,hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hb := b.property
  have he : (b : G) = r ^ 2 := square_eq_of_mem r hr (hB hb) (fun h => hb1 (Subtype.ext h))
    (elemPow_eq_one_of_isElementaryAbelian (b : G) hb)
  apply le_antisymm
  · intro x hx
    by_cases h1 : x=1
    · simp [h1]
    · rw [square_eq_of_mem r hr (hB hx) h1
        (elemPow_eq_one_of_isElementaryAbelian x hx)]
      exact mem_zpowers _
  · exact zpowers_le.mpr (he ▸ hb)
end OrthogonalFourBinary.CyclicFour

namespace OrthogonalFourBinary
open TerminalLines
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- A natural orthogonal invariant subspace excludes elementary offenders
inside every actual cyclic four-subgroup of the actor. -/
theorem no_offender_le_cyclicFour (ρ : Representation (ZMod 2) G V)
    (W : Subrepresentation ρ) (e : G ≃* IsometryGroup)
    (c : W.toSubmodule ≃ₗ[ZMod 2] Space)
    (hcoord : ∀ g v, c (W.toRepresentation g v) = (e g).val (c v))
    (r : G) (hr : orderOf r = 4) (B : Subgroup G) (hB : B ≤ zpowers r) :
    ¬ IsOffender ρ B := by
  intro hoff
  let := hoff.1.2
  have heq := CyclicFour.elementary_eq_square r hr B hB hoff.1.1
  have horder : orderOf (r ^ 2) = 2 := by rw [orderOf_pow, hr]; decide
  have hrank : rank B = 1 := by
    rw [heq, rank, Nat.card_zpowers, horder]
    decide
  have hcod : fixedCodim W.toRepresentation B = 2 := by
    rw [fixedCodim_map_equivariant W.toRepresentation naturalRepresentation
      e.toMonoidHom c hcoord,heq,e.toMonoidHom.map_zpowers]
    rw [map_pow]
    exact square_fixedCodim (e r) ((orderOf_injective e.toMonoidHom e.injective r).trans hr)
  have hle := fixedCodim_subrepresentation_le ρ W B
  have hh := hoff.2
  omega
end OrthogonalFourBinary
