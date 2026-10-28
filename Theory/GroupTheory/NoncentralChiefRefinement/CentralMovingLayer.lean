module
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# A central moving layer bounds the cubic commutator

Let H/O₂(H) be S₃ and suppose a complete chief series has at most one
noncentral binary factor. If a normal elementary subgroup W of Z(O₂(H))
is moved by O²(H), refining through W shows that [O₂(H),O²(H)] lies in W.
For each actual cubic subgroup A, its commutator with O₂(H) is consequently
abelian. Coprime idempotence makes its A-centralizer trivial. The established
cubic chief-count formula then bounds this commutator's order by four.

The source application recognizes the actual residual using the existing
small-cubic-commutator theorem. The moving central layer is essential to
that application: a sole noncentral binary factor by itself also permits
the quaternion layer in GL₂(3).

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), proof of
(6.5), printed p.398, the radius-one case.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H]

private theorem moving_layer_contains_residual_commutator
    (Q W : Subgroup H) [Q.Normal] [W.Normal]
    (hp : IsPGroup 2 Q) (hWQ : W ≤ Q)
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hc : s.noncentralTwoCount ≤ 1) (hw : ⁅W, pResidual 2 H⁆ ≠ ⊥) :
    ⁅Q, pResidual 2 H⁆ ≤ W := by
  let w : NormalNode H := ⟨W, inferInstanceAs W.Normal⟩
  let q : NormalNode H := ⟨Q, inferInstanceAs Q.Normal⟩
  obtain ⟨a, ha0, haw⟩ := exists_chiefSeries (⊥ : NormalNode H) w bot_le
  obtain ⟨b, hbw, hbq⟩ := exists_chiefSeries w q hWQ
  obtain ⟨c, hcq, hc1⟩ := exists_chiefSeries q ⊤ le_top
  have hab : a.last = b.head := haw.trans hbw.symm
  have hbc : (a.smash b hab).last = c.head :=
    (RelSeries.last_smash hab).trans (hbq.trans hcq.symm)
  have hcount : a.noncentralTwoCount + b.noncentralTwoCount + c.noncentralTwoCount ≤ 1 := by
    rw [← ChiefSeries.noncentralTwoCount_smash a b hab,
      ← ChiefSeries.noncentralTwoCount_smash (a.smash b hab) c hbc]
    rw [ChiefSeries.noncentralTwoCount_eq _ s (by simpa using ha0.trans h0.symm)
      (by simpa using hc1.trans h1.symm)]
    exact hc
  have hapos : a.noncentralTwoCount ≠ 0 := by
    intro hz
    have hpa : IsPGroup 2 a.last.val := (hp.to_le hWQ).of_equiv
      (MulEquiv.subgroupCongr (congrArg Subtype.val haw)).symm
    have hh := a.residual_commutator_le_head_of_count_zero hpa hz
    rw [ha0, haw] at hh
    exact hw (le_bot_iff.mp hh)
  have hbzero : b.noncentralTwoCount = 0 := by omega
  have hpb : IsPGroup 2 b.last.val := hp.of_equiv
    (MulEquiv.subgroupCongr (congrArg Subtype.val hbq)).symm
  have hh := b.residual_commutator_le_head_of_count_zero hpb hbzero
  simpa only [hbw, hbq, w, q] using hh

/-- A moving central elementary layer and the complete chief bound control
the literal commutator of every cubic subgroup with the original two-core. -/
theorem central_cubic_commutator_card_le_four
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (s : ChiefSeries H) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hc : s.noncentralTwoCount ≤ 1)
    (W : Subgroup H) [W.Normal] [IsElementaryAbelian 2 W]
    (hWQ : W ≤ pCore 2 H) (hWcentral : W ≤ centralizer (pCore 2 H : Set H))
    (hw : ⁅W, pResidual 2 H⁆ ≠ ⊥)
    (A : Subgroup H) (hA : Nat.card A = 3) :
    Nat.card (⁅pCore 2 H, A⁆ : Subgroup H) ≤ 4 := by
  let Q := pCore 2 H
  let C := ⁅Q, A⁆
  have hQp : IsPGroup 2 Q := pCore_isPGroup
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hAperfect : IsPPerfect 2 A := by
    apply (pResidual_eq_top_iff 2 A).mp
    apply top_unique
    intro a _
    apply mem_pResidual_of_orderOf_coprime
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (hA ▸ orderOf_dvd_natCard a)
  have hAR : A ≤ pResidual 2 H := le_pResidual_of_isPPerfect A hAperfect
  have hCW : C ≤ W := (commutator_mono le_rfl hAR).trans
    (moving_layer_contains_residual_commutator Q W hQp hWQ s h0 h1 hc hw)
  have hCQ : C ≤ Q := commutator_le_left _ _
  have hCp : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 W).to_le hCW
  let : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    ((hCW.trans hWcentral).trans (centralizer_le hCQ))
  have hAn : A ≤ normalizer (C : Set H) := normalizer_commutator_ge_right Q A
  have hid : ⁅C, A⁆ = C :=
    commutator_isPPerfect_idempotent A Q hAperfect hQp le_normalizer_of_normal
  have hcop : Nat.Coprime (Nat.card A) (Nat.card C) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) A C hAp hCp
  have hd : Disjoint C (C ⊓ centralizer (A : Set H)) := by
    simpa only [hid] using commutator_disjoint_centralizer_of_coprime C A hAn hcop
  have hfixed : (centralizer (A : Set H)).subgroupOf C = ⊥ := by
    apply bot_unique
    intro c hc'
    apply Subtype.ext
    exact (disjoint_iff.mp hd).le ⟨c.property, c.property, hc'⟩
  let := conjMulDistribMulActionOfLeNormalizer A C hAn
  have hfix : FixedPoints.subgroup A C = (centralizer (A : Set H)).subgroupOf C := by
    ext c
    constructor
    · intro hf a ha
      have hh := congrArg Subtype.val (hf ⟨a, ha⟩)
      change a * (c : H) * a⁻¹ = c at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro hf a
      apply Subtype.ext
      change (a : H) * (c : H) * (a : H)⁻¹ = c
      exact mul_inv_eq_iff_eq_mul.mpr (hf a a.property)
  have hcard : Nat.card C = 4 ^ conjugationCubicLength A C := by
    have hh := FixedPoints.index_eq_four_pow_cubicLength hAp hCp
    rw [← conjugationCubicLength_eq A C hAn, hfix, hfixed, index_bot] at hh
    exact hh
  let f : H →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hlen : conjugationCubicLength A Q ≤ 1 := by
    have hh := CubicComparison.symmetricThree_count f hf (hk ▸ hQp) A hA s h0 h1
    rw [hk] at hh
    rwa [← hh]
  change Nat.card C ≤ 4
  rw [hcard]
  exact (Nat.pow_le_pow_right (by decide) ((conjugationCubicLength_mono A hCQ).trans hlen)).trans_eq
    (by norm_num : 4 ^ 1 = 4)

end NoncentralChiefRefinement
