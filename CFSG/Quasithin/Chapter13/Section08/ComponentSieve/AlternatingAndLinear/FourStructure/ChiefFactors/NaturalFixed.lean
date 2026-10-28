module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic

/-!
# The natural Sylow fixed line

A Sylow two-subgroup fixes a nonzero vector and normalizes the unipotent
radical of its line. Sylow maximality puts the radical inside the Sylow
subgroup. Since the radical fixes exactly the line, the Sylow fixed space
has dimension one. Transport uses the specified group equivalence.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), the unique-maximal-submodule argument in 13.8.25,
printed p.961. No enumeration or group-order calculation is needed.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {E H : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Group H]

theorem sylow_fixedSpace_finrank [Finite E] (hE : 2 ∣ Nat.card E)
    (T : Sylow 2 (BinaryLinear.GL E)) :
    Module.finrank (ZMod 2) (BinaryLinear.fixedSpace (T : Subgroup (BinaryLinear.GL E))) = 1 := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (BinaryLinear.fixedSpace_ne_bot hE T.isPGroup')
  let W := Submodule.span (ZMod 2) {w}
  have hW0 : W ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw0
  have hTP : (T : Subgroup (BinaryLinear.GL E)) ≤ BinaryLinear.parabolic W := by
    intro x hx v
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      have he : a • w = v := by
        apply x.injective
        simpa only [map_smul, show x w = w from hw x hx] using ha
      exact Submodule.mem_span_singleton.mpr ⟨a, he⟩
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, show x w = w from hw x hx]
      exact W.smul_mem a (Submodule.mem_span_singleton_self w)
  have hRT : BinaryLinear.radical W ≤ (T : Subgroup (BinaryLinear.GL E)) := by
    have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right'
      (BinaryLinear.radical_two W) (hTP.trans (BinaryLinear.parabolic_le_normalizer W)))
      le_sup_left
    exact he ▸ le_sup_right
  have he : BinaryLinear.fixedSpace (T : Subgroup (BinaryLinear.GL E)) = W := by
    apply le_antisymm
    · intro v hv
      exact (BinaryLinear.mem_iff_fixed_radical hW0 v).mpr (fun g hg => hv g (hRT hg))
    · apply Submodule.span_le.mpr
      rintro v (rfl : v = w)
      exact hw
  rw [he]
  exact finrank_span_singleton hw0

theorem natural_sylow_fixedSpace_finrank [Finite E] (hE : 2 ∣ Nat.card E)
    (e : H ≃* BinaryLinear.GL E) (T : Sylow 2 H) :
    Module.finrank (ZMod 2) (fixedSpace (naturalAction e) (T : Subgroup H)) = 1 := by
  let : Finite (BinaryLinear.GL E) := Finite.of_injective
    (fun g : BinaryLinear.GL E => (g : E → E)) DFunLike.coe_injective
  let : Finite H := Finite.of_injective e e.injective
  let S := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : fixedSpace (naturalAction e) (T : Subgroup H) =
      BinaryLinear.fixedSpace (S : Subgroup (BinaryLinear.GL E)) := by
    ext v
    constructor
    · intro hv g hg
      obtain ⟨t, ht, rfl⟩ := hg
      exact hv ⟨t, ht⟩
    · intro hv t
      exact hv (e t) (Subgroup.mem_map_of_mem e.toMonoidHom t.property)
  rw [he]
  exact sylow_fixedSpace_finrank hE S
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
