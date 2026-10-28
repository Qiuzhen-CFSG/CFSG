module

public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The canonical subspace of a binary degree-four Sylow pair

If an order-nine subgroup R permutes with a Sylow two-subgroup S of GL₄(2),
the product RS has order at most 576 and is proper. Its full transvection
directions form a proper nonzero subspace: Sylow maximality supplies the
radical of a fixed line, and Gaussian elimination excludes all directions.
The normalizer of the pair preserves this canonically defined subspace.

This is the geometric step in the inner-action calculation for
Aschbacher–Smith, proof of Lemma 1.3.9, printed p.514, using the Sylow
hypothesis in the local setup of Proposition 1.3.4.
-/

@[expose] public section

open Subgroup
open scoped Pointwise MatrixGroups
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.FourCentralizerOvergroups
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation

abbrev Vec := Space 4
abbrev Lin := LinearGroup 4

local instance : Finite Lin := Finite.of_equiv _ (matrixEquivLinear 4).toEquiv

theorem card_linear : Nat.card Lin = 20160 := by
  rw [← Nat.card_congr (matrixEquivLinear 4).toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

theorem card_sylow (S : Sylow 2 Lin) : Nat.card S = 64 := by
  rw [S.card_eq_multiplicity, card_linear,
    show 20160 = 2 ^ 6 * 315 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]

theorem pair_join_ne_top (S : Sylow 2 Lin) (R : Subgroup Lin)
    (hR : Nat.card R = 9)
    (hperm : (R : Set Lin) * (S : Set Lin) = (S : Set Lin) * (R : Set Lin)) :
    R ⊔ (S : Subgroup Lin) ≠ ⊤ := by
  let m : R × S → ↥(R ⊔ (S : Subgroup Lin)) :=
    fun x => ⟨x.1.val * x.2.val, mul_mem_sup x.1.property x.2.property⟩
  have hm : Function.Surjective m := by
    intro x
    have hx : (x : Lin) ∈ (R : Set Lin) * (S : Set Lin) := by
      change (x : Lin) ∈ (R : Set Lin) * ((S : Subgroup Lin) : Set Lin)
      rw [← coe_sup_of_set_mul_comm R (S : Subgroup Lin) hperm]
      exact x.property
    obtain ⟨r, hr, s, hs, he⟩ := hx
    exact ⟨(⟨r, hr⟩, ⟨s, hs⟩), Subtype.ext he⟩
  have hc := Nat.card_le_card_of_surjective m hm
  rw [Nat.card_prod, hR, card_sylow] at hc
  intro ht
  rw [ht, card_top, card_linear] at hc
  omega

private theorem normalizer_direction {K : Subgroup Lin} {g : Lin}
    (hg : g ∈ normalizer (K : Set Lin)) {v : Vec} (hv : IsDirection K v) :
    IsDirection K (g v) := by
  intro f hf
  let f' := f.comp g.toLinearMap
  have hf' : f' v = 0 := hf
  have he : transvection (g v) f hf = g * transvection v f' hf' * g⁻¹ := by
    apply LinearEquiv.ext
    intro x
    change x + f x • g v = g (g.symm x + f' (g.symm x) • v)
    simp [f']
  rw [he]
  exact (hg _).mp (hv f' hf')

theorem normalizer_le_parabolic_directions (K : Subgroup Lin) :
    normalizer (K : Set Lin) ≤ parabolic (directions K) := by
  intro g hg v
  constructor
  · intro hv
    change IsDirection K v
    simpa using normalizer_direction ((normalizer (K : Set Lin)).inv_mem hg) hv
  · exact normalizer_direction hg

theorem directions_ne_bot_of_sylow_le (S : Sylow 2 Lin) {K : Subgroup Lin}
    (hSK : (S : Subgroup Lin) ≤ K) : directions K ≠ ⊥ := by
  have hV : 2 ∣ Nat.card Vec := by norm_num [Vec, Space, Nat.card_fun]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fixedSpace_ne_bot hV S.isPGroup')
  let W := Submodule.span (ZMod 2) {w}
  have hSP : (S : Subgroup Lin) ≤ parabolic W := by
    intro x hx v
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      refine Submodule.mem_span_singleton.mpr ⟨a, x.injective ?_⟩
      simpa only [map_smul, show x w = w from hw x hx] using ha
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, show x w = w from hw x hx]
      exact W.smul_mem a (Submodule.mem_span_singleton_self w)
  have hRS : radical W ≤ (S : Subgroup Lin) := by
    have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two W)
      (hSP.trans (parabolic_le_normalizer W))) le_sup_left
    exact he ▸ le_sup_right
  have hwD : w ∈ directions K := by
    intro f hf
    apply hSK
    apply hRS
    apply transvection_mem (Submodule.mem_span_singleton_self w)
    exact (Submodule.span_singleton_le_iff_mem w f.ker).mpr hf
  intro hbot
  exact hw0 (by simpa only [hbot, Submodule.mem_bot] using hwD)

theorem pair_subspace (S : Sylow 2 Lin) (R : Subgroup Lin)
    (hR : Nat.card R = 9)
    (hperm : (R : Set Lin) * (S : Set Lin) = (S : Set Lin) * (R : Set Lin)) :
    ∃ W : Submodule (ZMod 2) Vec, W ≠ ⊥ ∧ W ≠ ⊤ ∧ R ≤ parabolic W ∧
      normalizer (R : Set Lin) ⊓ normalizer (S : Set Lin) ≤ parabolic W := by
  let K := R ⊔ (S : Subgroup Lin)
  refine ⟨directions K, directions_ne_bot_of_sylow_le S le_sup_right, ?_,
    le_sup_left.trans (le_parabolic_directions K), ?_⟩
  · exact fun h => pair_join_ne_top S R hR hperm (eq_top_of_directions_eq_top K h)
  · exact (normalizer_inf_normalizer_le_normalizer_sup R (S : Subgroup Lin)).trans
      (normalizer_le_parabolic_directions K)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.InnerPairCalculation
