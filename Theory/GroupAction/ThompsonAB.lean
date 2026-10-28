module

public import Theory.GroupTheory.Commutator.ThompsonAB
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupAction.NormalizingFixedPoints
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Thompson's A × B lemma for group actions

Commuting subgroups A and B of a finite actor act on a finite p-group G.
For B a p-group and A = O^p(A), fixing C_G(B) pointwise forces A to fix G.
The semidirect product converts this assertion into the subgroup centralizer
lemma, without a commutativity assumption on G or a faithfulness assumption
on the whole actor.

For a faithful A-action, apply this result to the p-residual of the kernel K
of the action on C_G(B). It acts trivially on G, so faithfulness makes O^p(K)
trivial. Thus K is a normal p-subgroup of A and lies in O_p(A). In particular,
O_p(A) = 1 gives a faithful restricted action. This second conclusion in fact
does not need A = O^p(A).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.18 and its proof, printed p.24.
-/

open Subgroup

/-- Thompson's residual A × B lemma for an automorphism action. If A fixes
C_G(B) pointwise, it fixes all of G pointwise. -/
public theorem thompson_a_times_b_fixedPoints {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [MulDistribMulAction H G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup H) (hG : IsPGroup p G) (hB : IsPGroup p B)
    (hA : pResidual p A = ⊤) (hAB : ⁅A, B⁆ = ⊥)
    (hfix : A ≤ fixingSubgroup H (FixedPoints.subgroup B G : Set G)) :
    A ≤ fixingSubgroup H (Set.univ : Set G) := by
  let φ := MulDistribMulAction.toMulAut H G
  let S := G ⋊[φ] H
  let : Finite S := Finite.of_equiv (G × H) SemidirectProduct.equivProd.symm
  let i : G →* S := SemidirectProduct.inl
  let j : H →* S := SemidirectProduct.inr
  have hN : i.range.Normal := by
    change (SemidirectProduct.inl (φ := φ)).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let := hN
  have hAp : pResidual p (A.map j) = ⊤ :=
    (pResidual_eq_top_iff p _).mpr (((pResidual_eq_top_iff p _).mp hA).of_surjective
      (j.subgroupMap A) (j.subgroupMap_surjective A))
  have hBA : ⁅B.map j, A.map j⁆ = ⊥ := by
    rw [← map_commutator, commutator_comm B A, hAB, Subgroup.map_bot]
  have hfixed : i.range ⊓ centralizer (B.map j : Set S) ≤ centralizer (A.map j : Set S) := by
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    have hgb : g ∈ FixedPoints.subgroup B G := by
      intro b
      have hb := mem_centralizer_iff.mp hg (j b) (mem_map_of_mem j b.property)
      have hl := congrArg SemidirectProduct.left hb
      change (1 : G) * φ (b : H) g = g * φ 1 1 at hl
      simpa [φ, Subgroup.smul_def] using hl
    rw [mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have haf := ((mem_fixingSubgroup_iff H).mp (hfix ha)) g hgb
    apply SemidirectProduct.ext
    · change (1 : G) * φ a g = g * φ 1 1
      simpa [φ] using haf
    · change a * 1 = 1 * a
      simp
  have hc := thompson_a_times_b_centralizer (A.map j) (B.map j) i.range
    (hB.map j) (hG.of_surjective i.rangeRestrict i.rangeRestrict_surjective)
    hAp le_normalizer_of_normal le_normalizer_of_normal hBA hfixed
  intro a ha
  rw [mem_fixingSubgroup_iff]
  intro g _
  have hg := commutator_eq_bot_iff_le_centralizer.mp hc (show i g ∈ i.range from ⟨g, rfl⟩)
  have he := mem_centralizer_iff.mp hg (j a) (mem_map_of_mem j ha)
  have hl := congrArg SemidirectProduct.left he
  change (1 : G) * φ a g = g * φ 1 1 at hl
  simpa [φ] using hl


/-- For a faithful A-action, the kernel of its restriction to C_G(B) is
contained in O_p(A). No residual hypothesis on A is needed for this bound. -/
public theorem thompson_fixedPoints_kernel_le_pCore {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [MulDistribMulAction H G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup H) [FaithfulSMul A G]
    (hG : IsPGroup p G) (hB : IsPGroup p B) (hAB : ⁅A, B⁆ = ⊥) :
    fixingSubgroup A (FixedPoints.subgroup B G : Set G) ≤ pCore p A := by
  let C := FixedPoints.subgroup B G
  let : IsInvariant A G C := fixedPoints_isInvariant_of_normalizing_actor A B
    ((commutator_eq_bot_iff_le_centralizer.mp hAB).trans (centralizer_le_normalizer _))
  let f := MulDistribMulAction.toMulAut A C
  let K := f.ker
  let j : K →* H := A.subtype.comp K.subtype
  let R := (pResidual p K).map j
  have hR : pResidual p R = ⊤ := (pResidual_eq_top_iff p R).mpr
    ((isPPerfect_pResidual (G := K) p).of_surjective
      (j.subgroupMap (pResidual p K)) (j.subgroupMap_surjective (pResidual p K)))
  have hRA : R ≤ A := by
    rintro _ ⟨k, _, rfl⟩
    exact k.val.property
  have hRB : ⁅R, B⁆ = ⊥ := bot_unique ((commutator_mono hRA le_rfl).trans_eq hAB)
  have hRf : R ≤ fixingSubgroup H (C : Set G) := by
    rintro _ ⟨k, _, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro g hg
    have he := DFunLike.congr_fun (show f k.val = 1 from k.property) (⟨g, hg⟩ : C)
    exact congrArg Subtype.val he
  have htriv := thompson_a_times_b_fixedPoints R B hG hB hR hRB hRf
  have hres : pResidual p K = ⊥ := by
    apply bot_unique
    intro k hk
    rw [mem_bot]
    apply Subtype.ext
    apply faithfulSMul_iff.mp (inferInstance : FaithfulSMul A G)
    intro g
    have hm : j k ∈ R := mem_map.mpr ⟨k, hk, rfl⟩
    exact (mem_fixingSubgroup_iff H).mp (htriv hm) g (Set.mem_univ g)
  have hKp : IsPGroup p K := by
    have hq := isPGroup_quotient_pResidual (G := K) p
    exact (hq.of_equiv (QuotientGroup.quotientMulEquivOfEq hres)).of_equiv
      QuotientGroup.quotientBot
  have hKcore : K ≤ pCore p A := le_sSup ⟨inferInstance, hKp⟩
  intro a ha
  apply hKcore
  change f a = 1
  ext g
  exact (mem_fixingSubgroup_iff A).mp ha g.val g.property

/-- If O_p(A) = 1, a faithful A-action remains faithful on the B-fixed
subgroup, equipped with its actual restricted action. -/
public theorem thompson_faithfulSMul_fixedPoints {H G : Type*} [Group H] [Finite H] [Group G] [Finite G]
    [MulDistribMulAction H G] {p : ℕ} [Fact p.Prime]
    (A B : Subgroup H) [FaithfulSMul A G]
    (hG : IsPGroup p G) (hB : IsPGroup p B) (hAB : ⁅A, B⁆ = ⊥)
    (hcore : pCore p A = ⊥) :
    let : IsInvariant A G (FixedPoints.subgroup B G) :=
      fixedPoints_isInvariant_of_normalizing_actor A B
        ((commutator_eq_bot_iff_le_centralizer.mp hAB).trans (centralizer_le_normalizer _))
    FaithfulSMul A (FixedPoints.subgroup B G) := by
  let : IsInvariant A G (FixedPoints.subgroup B G) :=
    fixedPoints_isInvariant_of_normalizing_actor A B
      ((commutator_eq_bot_iff_le_centralizer.mp hAB).trans (centralizer_le_normalizer _))
  apply faithfulSMul_iff.mpr
  intro a ha
  have hak : a ∈ fixingSubgroup A (FixedPoints.subgroup B G : Set G) := by
    rw [mem_fixingSubgroup_iff]
    intro g hg
    exact congrArg Subtype.val (ha ⟨g, hg⟩)
  have hc := thompson_fixedPoints_kernel_le_pCore A B hG hB hAB hak
  rwa [hcore, mem_bot] at hc
