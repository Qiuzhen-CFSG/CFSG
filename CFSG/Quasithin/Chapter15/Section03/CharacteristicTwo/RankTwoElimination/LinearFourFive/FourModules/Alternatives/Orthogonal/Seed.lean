module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FourModules.Alternatives.Action

/-!
# The actual Sylow-central seed and its commutator projection

For a binary representation, a vector fixed by a Sylow two-subgroup has
an invariant representative modulo the commutator submodule. Sum its
translates over the left cosets: the sum is invariant, and its image in
coinvariants is the original vector because the Sylow index is odd.

Apply this to conjugation on the elementary abelian span `W_L`. Every
`z ∈ Z = Ω₁(Z(T))` is a product `u c`, where `u ∈ [W_L,L]`,
`c ∈ C_{W_L}(L)`, and `u` still centralizes `S ∩ L`. This is the
central-supplement part of B.2.14 needed by the orthogonal exclusion.
It uses the actual Sylow arrangement and the earlier elementarity of
`W_L`; it neither splits the orthogonal cover nor invokes module alternatives.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.13–14,
printed p.78, and the seed projection in 15.3.24, printed p.1129.
-/

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal

private theorem sylow_fixed_supplement {K V : Type*} [Group K] [Finite K]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) K V) (S : Sylow 2 K) (v : V)
    (hv : ∀ s : S, ρ s v = v) :
    ∃ c : V, (∀ g : K, ρ g c = c) ∧ v - c ∈ Representation.Coinvariants.ker ρ := by
  classical
  let _ := Fintype.ofFinite (K ⧸ (S : Subgroup K))
  let f : (K ⧸ (S : Subgroup K)) → V := Quotient.lift (fun g : K => ρ g v) (by
    intro a b hab
    have hh := hv ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩
    have h := congrArg (ρ a) hh
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] using h.symm)
  have hf (g : K) (q : K ⧸ (S : Subgroup K)) : f (g • q) = ρ g (f q) := by
    induction q using Quotient.inductionOn with
    | h a => exact LinearMap.congr_fun (ρ.map_mul g a) v
  let c : V := ∑ q, f q
  refine ⟨c, ?_, ?_⟩
  · intro g
    change ρ g (∑ q, f q) = ∑ q, f q
    rw [map_sum]
    simp_rw [← hf]
    exact Equiv.sum_comp (MulAction.toPerm g) f
  · apply (Representation.Coinvariants.mk_eq_iff ρ).mp
    have hq (q : K ⧸ (S : Subgroup K)) :
        Representation.Coinvariants.mk ρ (f q) = Representation.Coinvariants.mk ρ v := by
      induction q using Quotient.inductionOn with
      | h a => exact Representation.Coinvariants.mk_self_apply ρ a v
    have hi : Odd (Fintype.card (K ⧸ (S : Subgroup K))) := by
      rw [← Nat.card_eq_fintype_card]
      exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index (even_iff_two_dvd.mp he))
    change _ = Representation.Coinvariants.mk ρ (∑ q, f q)
    rw [map_sum]
    simp_rw [hq]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (R := ZMod 2),
      hi.natCast_zmod_two, one_smul]


variable {G : Type*} [Group G] (d : LocalData G) (L : Subgroup G)
  [IsElementaryAbelian 2 (d.componentSpan L)]

private noncomputable def spanRepresentation :
    Representation (ZMod 2) L (Additive (d.componentSpan L)) where
  toFun l := ((d.componentSpan L).normalizerMonoidHom
    ⟨l, le_normalizer_conjugateSpanBy d.V L l.property⟩).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change (1 : G) * u.toMul * 1⁻¹ = u.toMul
    simp
  map_mul' l k := by
    apply LinearMap.ext
    intro u
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((l : G) * k) * u.toMul * ((l : G) * k)⁻¹ =
      (l : G) * ((k : G) * u.toMul * (k : G)⁻¹) * (l : G)⁻¹
    group

private theorem span_coinvariants_le (v : Additive (d.componentSpan L))
    (hv : v ∈ Representation.Coinvariants.ker (spanRepresentation d L)) :
    (v.toMul : G) ∈ spanCommutator d L := by
  let U : Submodule (ZMod 2) (Additive (d.componentSpan L)) :=
    AddSubgroup.toZModSubmodule 2 ((spanCommutator d L).subgroupOf (d.componentSpan L)).toAddSubgroup
  have hU : Representation.Coinvariants.ker (spanRepresentation d L) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, w⟩, rfl⟩
    change (((spanRepresentation d L l w - w).toMul : d.componentSpan L) : G) ∈ spanCommutator d L
    simp only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    change (l : G) * w.toMul * (l : G)⁻¹ * (w.toMul : G)⁻¹ ∈ spanCommutator d L
    rw [spanCommutator, commutator_comm]
    exact commutator_mem_commutator l.property w.toMul.property
  exact hU hv

/-- A Sylow-central seed admits a component-central supplement to its
commutator projection, without any module-classification input. -/
theorem seed_decomposition [Finite G]
    (hS : Chapter1.IsSylowIn 2 (d.S ⊓ L) L) (z : G) (hz : z ∈ d.Z) :
    ∃ u : spanCommutator d L, ∃ c : d.componentSpan L,
      (c : G) ∈ centralizer (L : Set G) ∧ z = (u : G) * c ∧
      (u : G) ∈ centralizer (d.S ⊓ L : Set G) := by
  have hzW : z ∈ d.componentSpan L :=
    le_conjugateSpanBy d.V L (le_conjugateSpanBy d.Z d.M hz)
  obtain ⟨P, hP⟩ := hS
  have hfixed : ∀ p : P, spanRepresentation d L p.val (Additive.ofMul ⟨z, hzW⟩) =
      Additive.ofMul ⟨z, hzW⟩ := by
    intro p
    apply Additive.toMul.injective
    apply Subtype.ext
    change (p.val : G) * z * (p.val : G)⁻¹ = z
    have hpSL : (p.val : G) ∈ d.S ⊓ L := hP ▸ mem_map_of_mem L.subtype p.property
    have hc := centralInvolutions_le_centralizer_sylow d.T hz
      (p.val : G) (show (p.val : G) ∈ (d.T : Subgroup G) from hpSL.1.1)
    exact mul_inv_eq_iff_eq_mul.mpr hc
  obtain ⟨c, hc, hu⟩ := sylow_fixed_supplement (spanRepresentation d L) P
    (Additive.ofMul ⟨z, hzW⟩) hfixed
  have hu' : z * (c.toMul : G)⁻¹ ∈ spanCommutator d L :=
    by simpa only [toMul_sub, div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, toMul_ofMul] using
      span_coinvariants_le d L _ hu
  have hcentral : (c.toMul : G) ∈ centralizer (L : Set G) := by
    intro l hl
    have he := congrArg (fun w : Additive (d.componentSpan L) => (w.toMul : G)) (hc ⟨l, hl⟩)
    change l * (c.toMul : G) * l⁻¹ = c.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he
  refine ⟨⟨z * (c.toMul : G)⁻¹, hu'⟩, c.toMul, hcentral, ?_, ?_⟩
  · simp
  · have hzcentral : z ∈ centralizer (d.S ⊓ L : Set G) :=
      centralizer_le (inf_le_left.trans inf_le_left) (centralInvolutions_le_centralizer_sylow d.T hz)
    exact (centralizer (d.S ⊓ L : Set G)).mul_mem hzcentral
      ((centralizer (d.S ⊓ L : Set G)).inv_mem (centralizer_le inf_le_right hcentral))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Alternatives.Orthogonal

end
