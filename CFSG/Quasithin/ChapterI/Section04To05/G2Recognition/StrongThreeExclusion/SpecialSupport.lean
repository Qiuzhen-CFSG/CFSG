module

public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.SylowNineLocal
public import Theory.Character.InductionSpecialSupport

/-!
# Character induction on the original strongly three-embedded subgroup

In the Sylow-nine branch, a transporter between elements of H whose orders
are divisible by three already transports their cubic powers. The original
cubic transporter theorem therefore controls the entire three-singular
support, including elements of mixed order. Induction is an isometry for
class functions supported there.

These are consequences of the literal G₂(3) configuration. They do not
exclude the Sylow-nine branch or assume an ambient character table.
-/

public section
noncomputable section
attribute [local instance] Fintype.ofFinite
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

/-- The cubic transporter control applies to every three-singular element
of the original H. -/
theorem three_singular_transporter_mem_H
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G) (a b : c.H)
    (ha : 3 ∣ orderOf a) (g : G)
    (hg : g⁻¹ * (a : G) * g = (b : G)) : g ∈ c.H := by
  obtain ⟨t⟩ := exists_cubic_torus c
  have hS := t.cubic_plane_sylow_iff.mpr
    (t.small_cores_iff_not_cube_dvd.mpr hsmall)
  let k := orderOf a / 3
  have ha3 : orderOf (a ^ k) = 3 :=
    orderOf_pow_orderOf_div (orderOf_pos a).ne' ha
  have hpow : MulAut.conj g⁻¹ ((a ^ k : c.H) : G) = ((b ^ k : c.H) : G) := by
    change MulAut.conj g⁻¹ ((a : G) ^ k) = (b : G) ^ k
    rw [map_pow]
    congr 1
    simpa only [MulAut.conj_apply, inv_inv] using hg
  exact c.H.inv_mem_iff.mp
    (t.cubic_conjugator_mem_H_of_sylow hS (a ^ k) (b ^ k) ha3 g⁻¹ hpow)

/-- Special-support induction agrees on the original three-singular set. -/
theorem induced_three_singular_eq
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G)
    (φ : ClassFunction c.H) (hc : IsClassFunction φ)
    (hs : supportedOn φ {a : c.H | 3 ∣ orderOf a})
    (a : c.H) (ha : 3 ∣ orderOf a) :
    inducedClassFunction c.H φ a = φ a := by
  exact inducedClassFunction_eq_on_specialSupport c.H _
    (fun a b ha _ g hg => three_singular_transporter_mem_H c hsmall a b ha g hg)
    φ hc hs a ha

/-- Induction preserves the scalar product on the actual three-singular
support; no ambient irreducible-character data are premises. -/
theorem three_singular_induction_isometry
    (hsmall : ¬ 3 ^ 3 ∣ Nat.card G)
    (φ ψ : ClassFunction c.H) (hψ : IsClassFunction ψ)
    (hφ : supportedOn φ {a : c.H | 3 ∣ orderOf a})
    (hs : supportedOn ψ {a : c.H | 3 ∣ orderOf a}) :
    scalarProduct G (inducedClassFunction c.H φ) (inducedClassFunction c.H ψ) =
      scalarProduct c.H φ ψ := by
  exact scalarProduct_inducedClassFunction_of_specialSupport c.H _
    (fun a b ha _ g hg => three_singular_transporter_mem_H c hsmall a b ha g hg)
    φ ψ hψ hφ hs

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
