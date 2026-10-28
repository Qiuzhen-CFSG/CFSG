module

public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.AutomizerInvariants
public import Theory.SpecificGroups.PSL3Four.RootNormalizerModel.CubicGeometry
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.AutomorphismOddOuter
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Sylow

/-!
# Reducing root-automorphism conjugacy to a semilinear calculation

The inner automorphisms and the diagonal torus have orders 16 and 9,
respectively, and trivial intersection. Their join therefore has order 144.
An order-288 subgroup containing both normalizes this join, because its
relative index is two. If the diagonal torus is Sylow in the full automorphism
group, Sylow conjugacy puts it inside any order-288 subgroup after a change
of root coordinates. All four published automizer invariants survive that
literal change of coordinates, including the action on the intrinsic center.

This module proves those reductions. It does not assert that the torus is
Sylow in the full automorphism group or compute the normalizer of its join
with the inner subgroup. Those concrete structural results, and the subsequent
semilinear subgroup classification, remain separate proof obligations.

Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15(5–6), 46.3(2),
and 46.14, printed pp.29–30, 251, and 257–258. The coordinate maps are the
published `RootNormalizerModel` maps; no ambient recognition is imported.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
noncomputable section

/-- The literal inner-automorphism subgroup of the root carrier. -/
abbrev inner : Subgroup (MulAut Root) := (MulAut.conj : Root →* MulAut Root).range
/-- The two independent diagonal scalings. -/
abbrev torus : Subgroup (MulAut Root) := diagonalHom.range
/-- The order-144 subgroup normalized after Sylow alignment. -/
def innerTorus : Subgroup (MulAut Root) := inner ⊔ torus
/-- Diagonal scalings together with the separate graph and field involutions. -/
def semilinear : Subgroup (MulAut Root) := torus ⊔ zpowers graph ⊔ zpowers SylowModel.frob

theorem center_card : Nat.card (center Root) = 4 :=
  (Nat.card_congr (centerCongr rootEquiv).toEquiv).trans root_center_card

theorem inner_card : Nat.card inner = 16 := by
  have hk : (MulAut.conj : Root →* MulAut Root).ker = center Root := by
    ext x
    rw [MonoidHom.mem_ker, mem_center_iff]
    constructor
    · intro h y
      have he := DFunLike.congr_fun h y
      change x * y * x⁻¹ = y at he
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
    · intro h
      apply MulEquiv.ext
      intro y
      change x * y * x⁻¹ = y
      rw [← h y, mul_inv_cancel_right]
  have hc := (MulAut.conj : Root →* MulAut Root).ker.card_mul_index
  rw [index_ker, hk, center_card, SylowModel.card_U] at hc
  change 4 * Nat.card inner = 64 at hc
  omega

theorem torus_card : Nat.card torus = 9 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective Cubic.diagonalHom_injective).toEquiv,
    Nat.card_prod, Nat.card_units, card_F]

theorem inner_disjoint_torus : Disjoint inner torus := by
  apply disjoint_of_coprime_natCard
  rw [inner_card, torus_card]
  decide

theorem innerTorus_card : Nat.card innerTorus = 144 := by
  rw [innerTorus, card_sup_eq_mul_of_normalizes_of_disjoint inner torus
    (by rw [normalizer_eq_top]; exact le_top) inner_disjoint_torus,
    inner_card, torus_card]

theorem congr_eq_conj (a : MulAut Root) : MulAut.congr a = MulAut.conj a := by
  rfl

theorem inner_map (a : MulAut Root) :
    inner.map (MulAut.congr a).toMonoidHom = inner := by
  rw [congr_eq_conj]
  exact Normal.map_conj_eq inner a

theorem congr_mem_inner_iff (a b : MulAut Root) :
    MulAut.congr a b ∈ inner ↔ b ∈ inner := by
  simpa only [inner_map, MulEquiv.coe_toMonoidHom] using
    (mem_map_iff_mem (f := (MulAut.congr a).toMonoidHom) (K := inner) (x := b)
      (MulAut.congr a).injective)

/-- Transport all invariants, using the actual equivalence on the center. -/
theorem invariants_map {H : Subgroup (MulAut Root)} (h : AutomizerInvariants H)
    (a : MulAut Root) : AutomizerInvariants (H.map (MulAut.congr a).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change inner ≤ H.map (MulAut.congr a).toMonoidHom
    rw [← inner_map a]
    exact map_mono h.inner_le
  · rw [card_map_of_injective (MulAut.congr a).injective, h.card]
  · intro b
    let ec := centerCongr a
    obtain ⟨s, hs, he⟩ := h.full_center_action (MulAut.congr ec.symm b)
    refine ⟨MulAut.congr a s, mem_map_of_mem _ hs, ?_⟩
    intro z
    have hz := congrArg a (he (ec.symm z))
    change a (s (a.symm (z : Root))) =
      a (a.symm (b (ec (ec.symm z)) : Root)) at hz
    rw [ec.apply_symm_apply, a.apply_symm_apply] at hz
    exact hz
  · obtain ⟨c, hc, hcn, hc3, hcomm⟩ := h.central_cubic
    refine ⟨MulAut.congr a c, mem_map_of_mem _ hc,
      (congr_mem_inner_iff a c).not.mpr hcn, ?_, ?_⟩
    · rw [← map_pow]
      exact (congr_mem_inner_iff a (c ^ 3)).mpr hc3
    · rintro b ⟨s, hs, rfl⟩
      change ⁅(MulAut.congr a) c, (MulAut.congr a) s⁆ ∈ inner
      rw [← map_commutatorElement (MulAut.congr a)]
      exact (congr_mem_inner_iff a ⁅c, s⁆).mpr (hcomm s hs)

/-- Relative index two forces normalization of the inner–torus join. -/
theorem le_normalizer_innerTorus {H : Subgroup (MulAut Root)}
    (h : AutomizerInvariants H) (hT : torus ≤ H) : H ≤ normalizer (innerTorus : Set (MulAut Root)) := by
  have hK : innerTorus ≤ H := sup_le h.inner_le hT
  have hc : Nat.card (innerTorus.subgroupOf H) = 144 :=
    (Nat.card_congr (subgroupOfEquivOfLe hK).toEquiv).trans innerTorus_card
  have hi := (innerTorus.subgroupOf H).card_mul_index
  rw [hc, h.card] at hi
  have hn : (innerTorus.subgroupOf H).Normal := normal_of_index_eq_two (by omega)
  exact (normal_subgroupOf_iff_le_normalizer hK).mp hn

/-- Align a subgroup of order nine using Sylow conjugacy in the full automorphism group. -/
theorem exists_torus_le_map
    (hsyl : ∃ T : Sylow 3 (MulAut Root), (T : Subgroup (MulAut Root)) = torus)
    {H : Subgroup (MulAut Root)} (hcard : Nat.card H = 288) :
    ∃ a : MulAut Root, torus ≤ H.map (MulAut.congr a).toMonoidHom := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨T, hT⟩ := hsyl
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 3
    (n := 2) (by rw [hcard]; decide)
  let Q' : Subgroup (MulAut Root) := Q.map H.subtype
  have hQcard : Nat.card Q' = 9 := by
    rw [card_map_of_injective H.subtype_injective, hQ]
    norm_num
  have hQH : Q' ≤ H := by
    rintro _ ⟨q, _, rfl⟩
    exact q.property
  obtain ⟨S, hQS⟩ := (IsPGroup.of_card (p := 3) (n := 2) hQcard).exists_le_sylow
  have hScard : Nat.card (S : Subgroup (MulAut Root)) = 9 := by
    calc
      _ = Nat.card (T : Subgroup (MulAut Root)) := Nat.card_congr (S.equiv T).toEquiv
      _ = 9 := by rw [hT, torus_card]
  have hQS' : Q' = (S : Subgroup (MulAut Root)) :=
    eq_of_le_of_card_ge hQS (by rw [hScard, hQcard])
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (MulAut Root) S T
  refine ⟨a, ?_⟩
  intro x hx
  have hxT : x ∈ T := by change x ∈ (T : Subgroup (MulAut Root)); rwa [hT]
  rw [← ha] at hxT
  change x ∈ (↑(a • S) : Set (MulAut Root)) at hxT
  rw [Sylow.coe_smul] at hxT
  obtain ⟨y, hy, hxy⟩ := hxT
  exact ⟨y, hQH (hQS' ▸ hy), hxy⟩

end
end Matrix.PSL3Four.RootNormalizerModel.AutomizerConjugacy
