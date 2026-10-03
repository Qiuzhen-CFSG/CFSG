module

public import Stellmacher.Recognition.Parrott.ChosenCoreCenterLowerBound
public import Theory.GroupTheory.PGroup.OmegaHomomorphism

/-!
# Local reductions for the chosen omega subgroup

Retain the supplied involution, fixed join, and Sylow subgroup, and put
`S = C_G(z) ∩ C_G(a)`. If S covers the cyclic quotient of order four over
the two-core, Ω₁(S) is proper: its image has exponent two. Every element
of the derived core normalizes S. Its displacement on Ω₁(S) lies in S′
as soon as this is checked on the square-one generators.

These reductions do not assume the center order or pointwise centralization
of S′. Source: Parrott, *A characterization of the Tits' simple group*
(1972), p.676, the omega and inverter calculations.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Covering the order-four core quotient forces the chosen omega to be proper. -/
public theorem chosen_omega_ne_top_of_core_relIndex_four
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    (J.map H.subtype).relIndex S = 4 → omega₁ S (p := 2) ≠ ⊤ := by
  intro H J S hi htop
  obtain ⟨y, hy, hy4⟩ := d.chosen_centralizer_exists_quotient_order_four h hi
  let j : S →* H := inclusion inf_le_left
  let q := (QuotientGroup.mk' J).comp j
  obtain ⟨φ, _, ⟨e⟩⟩ := h.quotient_model
  let f := e.toMonoidHom.comp q
  have hp : IsPGroup 2 f.range :=
    (d.chosen_centralizer_isPGroup h).of_surjective f.rangeRestrict
      f.rangeRestrict_surjective
  let : IsCyclic f.range :=
    (SemidirectProduct.two_subgroup_isCyclic_card_dvd_four φ f.range hp).1
  let s : S := ⟨y, hy⟩
  have hs : s ∈ omega₁ S (p := 2) := htop ▸ mem_top s
  have hs2 := f.rangeRestrict.square_eq_one_on_omega₁ hs
  have hf2 : (f s) ^ 2 = 1 := congrArg Subtype.val hs2
  have hq2 : (QuotientGroup.mk' J y) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact hf2
  have hd := orderOf_dvd_of_pow_eq_one hq2
  rw [hy4] at hd
  norm_num at hd

/-- Every supplied element of the derived core normalizes the actual S.
In particular this applies to every w outside the supplied fixed join. -/
public theorem chosen_derived_mem_normalizer
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ w : G, w ∈ E → w ∈ normalizer (S : Set G) := by
  exact d.derived_le_chosen_centralizer_normalizer h

/-- The desired displacement on the actual omega is equivalent to the same
calculation on square-one elements of S, with the supplied w unchanged. -/
public theorem chosen_omega_displacement_iff_square_one
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let E := (commutator (pCore 2 H)).map (H.subtype.comp (pCore 2 H).subtype)
    let S := H ⊓ centralizer ({(d.a : G)} : Set G)
    ∀ (w : G) (hw : w ∈ E),
      (∀ v ∈ omega₁ S (p := 2),
        v⁻¹ * S.normalizerMonoidHom
          ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S) ↔
      (∀ v : S, v ^ 2 = 1 →
        v⁻¹ * S.normalizerMonoidHom
          ⟨w, d.chosen_derived_mem_normalizer h w hw⟩ v ∈ commutator S) := by
  intro H E S w hw
  exact (S.normalizerMonoidHom
    ⟨w, d.chosen_derived_mem_normalizer h w hw⟩).toMonoidHom.displacement_on_omega₁_iff

end Stellmacher.Recognition.ParrottSecondElementaryData
