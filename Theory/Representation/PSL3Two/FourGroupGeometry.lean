module

public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank
public import Theory.GroupAction.CommonFixedNormalizer
public import Theory.GroupTheory.PResidual.FiniteImage

/-!+# Four-group geometry: fixed spaces and transport principles

The full automorphism group has elementary two-subgroups of order at most four,
and its two-residual is inner. The fixed space below uses the literal natural
and contragredient matrix actions, restricted to the preimage of an inner actor.

The final transport principle avoids prescribing an outer-action formula: if
the inner pointwise fixer of a fixed subgroup is exactly the acting subgroup,
then every pointwise fixer normalizes that subgroup. An inner normalizer then
excludes outer pointwise fixers in any extending representation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
paragraph of the proof of 15.3.61(2), printed p.1151.
-/

public section
open Subgroup Theory.GroupTheory
namespace BinaryLinearThree.FourGroupGeometry

/-- Natural plus contragredient coordinates, retaining the actual dual space. -/
abbrev NaturalDual := Vector × Module.Dual (ZMod 2) Vector

/-- The common fixed space of the inner preimage of an automorphism subgroup. -/
@[expose] noncomputable def naturalDualFixed (A : Subgroup (MulAut Group)) :
    Submodule (ZMod 2) NaturalDual :=
  Representation.BinaryOffender.fixedSpace (W.prod W.dual) (A.comap MulAut.conj)

theorem mem_naturalDualFixed (A : Subgroup (MulAut Group)) (w : NaturalDual) :
    w ∈ naturalDualFixed A ↔ ∀ g : Group, MulAut.conj g ∈ A →
      (W g w.1, W.dual g w.2) = w := by
  change (∀ g : A.comap MulAut.conj, (W g.val w.1, W.dual g.val w.2) = w) ↔ _
  exact Subtype.forall

/-- The full automorphism bound, including elementary groups meeting the outer coset. -/
theorem elementary_card_le_four (A : Subgroup (MulAut Group))
    (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 4 := by
  have hr : primeRank 2 (MulAut Group) ≤ 2 := by
    rw [primeRank_equiv 2 (MulAut.congr Matrix.PSL3Two.equiv)]
    exact (Matrix.PSL3Even.automorphism_two_rank_eq_of_card_two (ZMod 2)
      (by simp)).le
  exact (primeRank_le_iff_elementary_card_le _).mp hr A hA

/-- The two-residual is contained in the inner subgroup, since the outer quotient is C₂. -/
theorem twoResidual_le_inner : pResidual 2 (MulAut Group) ≤ MulAut.innerSubgroup Group :=
  sInf_le ⟨inferInstance, Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup⟩

private theorem inverse_fixes {K V : Type*} [_root_.Group K] [_root_.Group V]
    (ρ : K →* MulAut V) (a : K) (w : V) (h : ρ a w = w) : ρ a⁻¹ w = w := by
  have hh := congrArg (ρ a⁻¹) h
  simpa only [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    MulAut.one_apply] using hh.symm

/-- An inner pointwise-fixer calculation and an inner normalizer exclude every
outer pointwise fixer. No action formula outside the normal subgroup is needed. -/
theorem pointwise_fixer_mem_of_inner {K V : Type*} [_root_.Group K] [_root_.Group V]
    (ρ : K →* MulAut V) (I A : Subgroup K) [I.Normal] (hAI : A ≤ I)
    (hN : normalizer (A : Set K) ≤ I)
    (hinner : ∀ b ∈ I, (∀ w ∈ ρ.commonFixed A, ρ b w = w) → b ∈ A)
    (a : K) (ha : ∀ w ∈ ρ.commonFixed A, ρ a w = w) : a ∈ A := by
  have hconj (c : K) (hc : ∀ w ∈ ρ.commonFixed A, ρ c w = w)
      (b : K) (hb : b ∈ A) : c * b * c⁻¹ ∈ A := by
    apply hinner _ ((inferInstance : I.Normal).conj_mem b (hAI hb) c)
    intro w hw
    calc
      ρ (c * b * c⁻¹) w = ρ c (ρ b (ρ c⁻¹ w)) := by
        simp only [map_mul, MulAut.mul_apply]
      _ = ρ c (ρ b w) := by rw [inverse_fixes ρ c w (hc w hw)]
      _ = ρ c w := by rw [(MonoidHom.mem_commonFixed ρ A w).mp hw b hb]
      _ = w := hc w hw
  have hn : a ∈ normalizer (A : Set K) := by
    rw [mem_normalizer_iff]
    intro b
    refine ⟨hconj a ha b, ?_⟩
    intro hb
    have h := hconj a⁻¹ (fun w hw => inverse_fixes ρ a w (ha w hw)) _ hb
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
      mul_one] using h
  exact hinner a (hN hn) ha

/-- An ambient isomorphism identifies the actual subgroup normalizers. -/
noncomputable def normalizerEquivMap {K L : Type*} [_root_.Group K] [_root_.Group L]
    (e : K ≃* L) (A : Subgroup K) :
    normalizer (A : Set K) ≃* normalizer (A.map e.toMonoidHom : Set L) :=
  (e.subgroupMap (normalizer (A : Set K))).trans
    (MulEquiv.subgroupCongr (map_equiv_normalizer_eq A e))

/-- The size of the conjugation image of a normalizer is invariant under an
ambient isomorphism; the proof transports the action, not just the subgroup order. -/
theorem card_normalizerActionRange_map {K L : Type*} [_root_.Group K] [_root_.Group L]
    (e : K ≃* L) (A : Subgroup K) :
    Nat.card (A.map e.toMonoidHom).normalizerMonoidHom.range =
      Nat.card A.normalizerMonoidHom.range := by
  let eA : A ≃* A.map e.toMonoidHom := e.subgroupMap A
  let eN := normalizerEquivMap e A
  have he : (MulAut.congr eA).toMonoidHom.comp A.normalizerMonoidHom =
      (A.map e.toMonoidHom).normalizerMonoidHom.comp eN.toMonoidHom := by
    apply MonoidHom.ext
    intro n
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := eA.surjective x
    apply Subtype.ext
    change e ((n : K) * (eA.symm (eA y) : A) * (n : K)⁻¹) =
      e (n : K) * e (y : K) * (e (n : K))⁻¹
    rw [eA.symm_apply_apply, map_mul, map_mul, map_inv]
  have hr := congrArg MonoidHom.range he
  have htop : eN.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr eN.surjective
  rw [MonoidHom.range_comp, MonoidHom.range_comp,
    htop, ← MonoidHom.range_eq_map] at hr
  rw [← hr]
  exact (Nat.card_congr ((MulAut.congr eA).subgroupMap A.normalizerMonoidHom.range).toEquiv).symm

end BinaryLinearThree.FourGroupGeometry
