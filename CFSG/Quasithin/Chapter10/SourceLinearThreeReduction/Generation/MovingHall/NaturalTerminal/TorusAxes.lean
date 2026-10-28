module

public import Theory.Representation.PairedScalarAxes
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# General-field Cartan alignment in the moving natural row

The actual normalizer action on the original elementary subgroup is marked
by two independent scalar coordinates. The cyclic selected torus has order
`2^m - 1`, hence `m ≤ n`. Its source fixed-space dimension is `2*n - m`,
which is positive. The scalar fixed-space calculation then gives dimension
`n`, so `m = n` and the selected torus equals a Cartan axis.

This is the calculation in Aschbacher–Smith 10.2.3(4), printed p.746. The
moving-Hall assembly owner must construct the scalar marking and obtain the
fixed-space dimension from the earlier-source elementary decomposition.
No field-order-four or exponent-three hypothesis is used.
-/

public section
open Subgroup
open Representation Representation.BinaryOffender Representation.BinaryConjugationSection
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.MovingHall
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [Algebra (ZMod 2) F]

/-- The source fixed-space dimension forces the selected cyclic torus to be
one of the two original Cartan axes, with the full field degree. -/
theorem cartan_axis_of_fixed_dimension (D D₁ D₂ P E : Subgroup G) [IsElementaryAbelian 2 E]
    (hDE : D ≤ normalizer (E : Set G))
    (q₁ q₂ : D →* Fˣ)
    (hfaith : q₁.ker ⊓ q₂.ker = ⊥)
    (haxes₁ : q₂.ker.map D.subtype = D₁) (haxes₂ : q₁.ker.map D.subtype = D₂)
    (hD₁ : Nat.card D₁ = Nat.card F - 1) (hD₂ : Nat.card D₂ = Nat.card F - 1)
    (c : Additive E ≃ₗ[ZMod 2] F × F)
    (he : ∀ (d : D) (x : E),
      c (Additive.ofMul (E.normalizerMonoidHom (inclusion hDE d) x)) =
        ((q₁ d : F) * (c (Additive.ofMul x)).1,
         (q₂ d : F) * (c (Additive.ofMul x)).2))
    (hPD : P ≤ D) [IsCyclic P]
    (m n : ℕ) (hm : 1 < m) (hF : Nat.card F = 2 ^ n)
    (hP : Nat.card P = 2 ^ m - 1)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace (originalNormalizerAction hDE) (P.subgroupOf D)) = 2*n-m) :
    m = n ∧ (P = D₁ ∨ P = D₂) := by
  let ρ := originalNormalizerAction hDE
  let Q := P.subgroupOf D
  have hQcard : Nat.card Q = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe hPD).toEquiv
  have hdimF : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa only [Nat.card_zmod, hF] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)).symm
  have he' : ∀ d x, c (ρ d x) = ((q₁ d : F) * (c x).1, (q₂ d : F) * (c x).2) :=
    fun d x => by
      have hx := originalNormalizerAction_apply hDE d x
      have hx' := congrArg (fun y : E => c (Additive.ofMul y)) hx
      exact hx'.trans (he d x.toMul)
  let : IsCyclic Q := (subgroupOfEquivOfLe hPD).isCyclic.mpr inferInstance
  have hdiv : 2^m-1 ∣ 2^n-1 := by
    have hd := PairedScalarAxes.cyclic_card_dvd_units q₁ q₂ hfaith Q
    simpa only [hQcard, hP, Nat.card_units, hF] using hd
  have hn : 0 < n := by
    have hcard := Finite.one_lt_card (α := F)
    rw [hF] at hcard
    by_contra hn
    have : n = 0 := by omega
    simp [this] at hcard
  have hmn : m ≤ n := by
    have hle := Nat.le_of_dvd (show 0 < 2^n-1 by have := Nat.one_lt_pow hn.ne' (by decide : 1 < 2); omega) hdiv
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    have hpowm : 0 < 2^m := pow_pos (by decide) _
    have hpown : 0 < 2^n := pow_pos (by decide) _
    omega
  have hQ : Q ≠ ⊥ := by
    apply (one_lt_card_iff_ne_bot Q).mp
    rw [hQcard,hP]
    have h4 : 2^2 ≤ 2^m := Nat.pow_le_pow_right (by decide) hm
    omega
  obtain ⟨hk,hfix⟩ := PairedScalarAxes.axis_and_fixed_finrank ρ q₁ q₂ c he' hfaith Q hQ
    (by change 0 < Module.finrank (ZMod 2) (fixedSpace (originalNormalizerAction hDE) Q)
        rw [hdim]; omega)
  have hmn' : m = n := by
    change Module.finrank (ZMod 2) (fixedSpace (originalNormalizerAction hDE) Q) = _ at hfix
    rw [hdim, hdimF] at hfix
    omega
  refine ⟨hmn', ?_⟩
  rcases hk with hk | hk
  · right
    apply eq_of_le_of_card_ge
    · intro p hp
      rw [← haxes₂]
      exact mem_map.mpr ⟨⟨p,hPD hp⟩,hk hp,rfl⟩
    · rw [hD₂,hF,hP,hmn']
  · left
    apply eq_of_le_of_card_ge
    · intro p hp
      rw [← haxes₁]
      exact mem_map.mpr ⟨⟨p,hPD hp⟩,hk hp,rfl⟩
    · rw [hD₁,hF,hP,hmn']

/-- A full paired-torus marking supplies the two axis orders, so the only
source dimension input is that of the original fixed subgroup. -/
theorem cartan_axis_of_paired_torus (D P E : Subgroup G) [IsElementaryAbelian 2 E]
    (hDE : D ≤ normalizer (E : Set G))
    (q₁ q₂ : D →* Fˣ)
    (hq : Function.Bijective (fun d => (q₁ d, q₂ d)))
    (c : Additive E ≃ₗ[ZMod 2] F × F)
    (he : ∀ (d : D) (x : E),
      c (Additive.ofMul (E.normalizerMonoidHom (inclusion hDE d) x)) =
        ((q₁ d : F) * (c (Additive.ofMul x)).1,
         (q₂ d : F) * (c (Additive.ofMul x)).2))
    (hPD : P ≤ D) [IsCyclic P]
    (m n : ℕ) (hm : 1 < m) (hF : Nat.card F = 2 ^ n)
    (hP : Nat.card P = 2 ^ m - 1)
    (hdim : Module.finrank (ZMod 2)
      (fixedSpace (originalNormalizerAction hDE) (P.subgroupOf D)) = 2*n-m) :
    m = n ∧ (P = q₂.ker.map D.subtype ∨ P = q₁.ker.map D.subtype) := by
  have hfaith : q₁.ker ⊓ q₂.ker = ⊥ := by
    apply bot_unique
    intro d hd
    change d = 1
    apply hq.injective
    simpa only [map_one] using
      (Prod.ext (show q₁ d = 1 from hd.1) (show q₂ d = 1 from hd.2))
  have hswap : Function.Bijective (fun d => (q₂ d, q₁ d)) :=
    (Equiv.prodComm Fˣ Fˣ).bijective.comp hq
  have hc₁ : Nat.card (q₁.ker.map D.subtype) = Nat.card F - 1 := by
    rw [card_map_of_injective D.subtype_injective,
      PairedScalarAxes.card_coordinate_kernel q₁ q₂ hq, Nat.card_units]
  have hc₂ : Nat.card (q₂.ker.map D.subtype) = Nat.card F - 1 := by
    rw [card_map_of_injective D.subtype_injective,
      PairedScalarAxes.card_coordinate_kernel q₂ q₁ hswap, Nat.card_units]
  exact cartan_axis_of_fixed_dimension D _ _ P E hDE q₁ q₂ hfaith rfl rfl
    hc₂ hc₁ c he hPD m n hm hF hP hdim

end CFSG.Quasithin.Chapter10.MovingHall
