module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankOne

/-!
# Algebraic bounds at the original critical endpoint

Conjugating the source 13.7.3(7) bound for C_H(U_H) yields the required
commutator bound at Gγ. The line order is preserved by the same conjugator.
The actual star-image order and corrected 13.8.10 give both denominator
indices, and a strict binary rank bound gives the required group order.

The earlier kernel identity, proper denominator, index comparison and
base centralizer bound remain explicit source inputs. These lemmas do not
construct a reversed critical configuration or assert GeometricBounds.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.7.3(7),
13.8.10–11 and the last paragraph of 13.8.13, printed pp.950–951.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
open CriticalGeometry
variable {G : Type*} [Group G]
variable {L T H V : Subgroup G} (c : CriticalPair L T H V)

theorem endpoint_line_card (V₁ : Subgroup G) (hline : Nat.card V₁ = 2) :
    Nat.card (c.Aone V₁) = 2 := by
  rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj (c.gb : G)).injective, hline]

theorem centralizer_commutator_bound (V₃ V₁ : Subgroup G)
    (hUH : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (h137 : ⁅Source.HC H V₃, Source.VH H V⁆ ≤ V₁) :
    ⁅Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤ c.Aone V₁ := by
  let e := MulAut.conj (c.gb : G)
  have hC : Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G) ≤
      (Source.HC H V₃).map e.toMonoidHom := by
    intro x hx
    rw [mem_map_equiv]
    refine ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · have hh := hUH hx.1
      rw [c.vertexGroup_gamma, mem_map_equiv] at hh
      exact hh
    · intro u hu
      apply e.injective
      have hh := mem_centralizer_iff.mp hx.2 (e u)
        (mem_map_of_mem e.toMonoidHom hu)
      simpa only [map_mul, e.apply_symm_apply] using hh
  have hc := map_mono (f := e.toMonoidHom) h137
  rw [map_commutator] at hc
  exact (commutator_mono hC le_rfl).trans hc

theorem denominator_indices [Finite G] (V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (a : StarAction H (Source.UH H V₃) V₁) {P : Subgroup G}
    (f : RankOneFactors a P (c.Ugamma V₃))
    (hUγ : c.Ugamma V₃ ≤ H)
    (hkernel : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) <
      Source.UH H V₃)
    (hcomparison :
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃) ≤
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)) :
    (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
        (Source.UH H V₃) = 2 ∧
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) = 2 := by
  have hγ : (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
      (c.Ugamma V₃) = 2 := by
    rw [hkernel, inf_relIndex_left, ← starImage_card H (c.Ugamma V₃) hUγ]
    exact f.actor_card
  exact ⟨corrected_13_8_10_index _ _ _ _ hproper hcomparison hγ, hγ⟩
/-- Convert the strict binary rank conclusion of 13.8.11 to the required order bound. -/
theorem card_gt_two_of_rank_gt_one {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W]
    (h : 1 < Module.finrank (ZMod 2) (Additive W)) : 2 < Nat.card W := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
  change Nat.card W = _ at hc
  rw [hc, Nat.card_zmod]
  simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1 < 2) h

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
