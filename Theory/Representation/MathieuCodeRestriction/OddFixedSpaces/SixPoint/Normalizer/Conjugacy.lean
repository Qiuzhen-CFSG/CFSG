module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Normalizer.Representative
public import Theory.Mathieu.M24.Properties.Transitivity
public import Mathlib.GroupTheory.Sylow

/-!
# Conjugacy and the six-point normalizer image

A pointwise five-point stabilizer has order 48. Its subgroups of order three
are Sylow subgroups, so Sylow conjugacy adjusts a five-transitive transporter
to conjugate the prescribed cubic subgroups. In particular every cubic with
six fixed points is conjugate to the explicitly checked representative.
With the same subgroup at both ends, the transporter realizes every
permutation of five of its six fixed points; the sixth image is forced.
Thus the actual restricted normalizer action is onto the symmetric group.

Source: Aschbacher–Smith H.15.7(1–2), printed pp.401–402. The kernel and the
sextet complement are separate assertions, not consequences asserted here.
-/

@[expose] public section

open Sporadic.Mathieu
namespace MathieuCode.SixPoint
noncomputable section
open scoped Pointwise

/-- Five distinct native points have pointwise stabilizer of order 48. -/
theorem fivePointStabilizer_card (e : Fin 5 ↪ Fin 24) :
    Nat.card (fixingSubgroup M24 (Set.range e)) = 48 := by
  have hn : (Set.range e).ncard = 5 := by
    rw [Set.ncard_range_of_injective e.injective]
    simp
  have hi := MulAction.IsMultiplyPretransitive.index_of_fixingSubgroup_eq
    (Set.range e) (hn.symm ▸ m24_isFivePretransitive)
  have he := (fixingSubgroup M24 (Set.range e)).card_mul_index
  rw [hi, hn, Nat.card_fin, m24_order] at he
  norm_num [Nat.choose, Nat.factorial] at he
  omega

private theorem conjugate_three_in_fortyeight (H A B : Subgroup M24)
    (hH : Nat.card H = 48) (hA : Nat.card A = 3) (hB : Nat.card B = 3)
    (hAH : A ≤ H) (hBH : B ≤ H) :
    ∃ h : H, A.map (MulAut.conj h.val).toMonoidHom = B := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have ha : Nat.card (A.subgroupOf H) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv).trans hA
  have hb : Nat.card (B.subgroupOf H) = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv).trans hB
  have hp : 3 ^ (Nat.card H).factorization 3 = 3 := by
    rw [hH, show 48 = 3 * 16 by decide, Nat.factorization_mul (by decide) (by decide)]
    norm_num [(by decide : Nat.Prime 3).factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 16)]
  let P : Sylow 3 H := Sylow.ofCard (A.subgroupOf H) (ha.trans hp.symm)
  let Q : Sylow 3 H := Sylow.ofCard (B.subgroupOf H) (hb.trans hp.symm)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P Q
  have hh' : (A.subgroupOf H).map (MulAut.conj h).toMonoidHom = B.subgroupOf H :=
    congrArg Sylow.toSubgroup hh
  have hc : (MulAut.conj h.val).toMonoidHom.comp H.subtype =
      H.subtype.comp (MulAut.conj h).toMonoidHom := by ext x; rfl
  refine ⟨h, ?_⟩
  calc
    A.map (MulAut.conj h.val).toMonoidHom =
        ((A.subgroupOf H).map H.subtype).map (MulAut.conj h.val).toMonoidHom := by
      rw [Subgroup.map_subgroupOf_eq_of_le hAH]
    _ = ((A.subgroupOf H).map (MulAut.conj h).toMonoidHom).map H.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map, hc]
    _ = B := by rw [hh', Subgroup.map_subgroupOf_eq_of_le hBH]

/-- Conjugacy can be arranged to match any prescribed five fixed points. -/
theorem exists_conjugator_matching_five (D E : Subgroup M24)
    (hD : Nat.card D = 3) (hE : Nat.card E = 3)
    (a : Fin 5 ↪ FixedPoint D) (b : Fin 5 ↪ FixedPoint E) :
    ∃ g : M24, D.map (MulAut.conj g).toMonoidHom = E ∧
      ∀ i, g • (a i).val = (b i).val := by
  let a' : Fin 5 ↪ Fin 24 := a.trans (Function.Embedding.subtype _)
  let b' : Fin 5 ↪ Fin 24 := b.trans (Function.Embedding.subtype _)
  obtain ⟨g, hg⟩ := m24_isFivePretransitive.exists_smul_eq a' b'
  have hg' (i : Fin 5) : g • (a i).val = (b i).val :=
    congrArg (fun e : Fin 5 ↪ Fin 24 => e i) hg
  let H := fixingSubgroup M24 (Set.range b')
  have hDH : D.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro x ⟨d, hd, rfl⟩
    apply (mem_fixingSubgroup_iff M24).mpr
    rintro y ⟨i, rfl⟩
    change (g * d * g⁻¹) • (b i).val = (b i).val
    rw [← hg' i, mul_smul, mul_smul, inv_smul_smul]
    exact congrArg (g • ·) ((a i).property ⟨d, hd⟩)
  have hEH : E ≤ H := by
    intro d hd
    apply (mem_fixingSubgroup_iff M24).mpr
    rintro y ⟨i, rfl⟩
    exact (b i).property ⟨d, hd⟩
  obtain ⟨h, hh⟩ := conjugate_three_in_fortyeight H _ E
    (fivePointStabilizer_card b')
    ((Subgroup.card_map_of_injective (MulAut.conj g).injective).trans hD) hE hDH hEH
  refine ⟨h.val * g, ?_, ?_⟩
  · rw [Subgroup.map_map] at hh
    convert hh using 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  · intro i
    rw [mul_smul, hg' i]
    exact (mem_fixingSubgroup_iff M24).mp h.property _ ⟨i, rfl⟩

theorem cubicSubgroup_conjugacy (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    ∃ g : M24, D.map (MulAut.conj g).toMonoidHom = cubicSubgroup := by
  obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card (FixedPoint D) by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using (show 5 ≤ Nat.card (FixedPoint D) by omega))
  obtain ⟨b⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 5) ≤ Fintype.card (FixedPoint cubicSubgroup) by
      rw [← Nat.card_eq_fintype_card (α := FixedPoint cubicSubgroup),
        cubicSubgroup_fixed_card, Fintype.card_fin]; decide)
  obtain ⟨g, hg, _⟩ := exists_conjugator_matching_five D cubicSubgroup hD cubicSubgroup_card a b
  exact ⟨g, hg⟩

private theorem perm_ext_except {α : Type*} (σ τ : Equiv.Perm α) (a : α)
    (h : ∀ x, x ≠ a → σ x = τ x) : σ = τ := by
  apply Equiv.ext
  intro x
  by_cases hx : x = a
  · subst x
    by_cases he : τ.symm (σ a) = a
    · simpa only [τ.apply_symm_apply] using congrArg τ he
    · have hh := h (τ.symm (σ a)) he
      rw [τ.apply_symm_apply] at hh
      exact (he (σ.injective hh)).elim
  · exact h x hx

/-- The literal normalizer action induces all permutations of the six fixed points. -/
theorem normalizerPerm_surjective (D : Subgroup M24)
    (hD : Nat.card D = 3) (hfix : Nat.card (FixedPoint D) = 6) :
    Function.Surjective (normalizerPerm D) := by
  classical
  let e : Fin 6 ≃ FixedPoint D :=
    (Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hfix)).symm
  let a : Fin 5 ↪ FixedPoint D := Fin.castSuccEmb.trans e.toEmbedding
  intro σ
  let b : Fin 5 ↪ FixedPoint D := a.trans σ.toEmbedding
  obtain ⟨g, hg, happ⟩ := exists_conjugator_matching_five D D hD hD a b
  let n : Subgroup.normalizer (D : Set M24) :=
    ⟨g, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hg⟩
  refine ⟨n, perm_ext_except _ σ (e (Fin.last 5)) ?_⟩
  intro x hx
  have hlast : e.symm x ≠ Fin.last 5 := by
    intro he
    apply hx
    rw [← he, e.apply_symm_apply]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.mpr hlast
  have hix : a i = x := by
    change e i.castSucc = x
    rw [hi, e.apply_symm_apply]
  rw [← hix]
  exact Subtype.ext (happ i)

end
end MathieuCode.SixPoint
