module

public import Theory.Representation.RegularCyclicNormalClosure.Seed
public import Theory.SpecificGroups.Frobenius21.Recognition

/-!
# Assembling the conjugates of a regular cyclic local factor

Given a `FactorSeed`, enumerate the distinct actual conjugates of its subgroup
and use their displacement spans as summands. Conjugation transports local
complementarity and cross-fixation; faithfulness then gives commuting independent
group factors. The supremum of these factors is the normal closure of C.

For the global module splitting, combine complementary pairs whose moved spaces
lie in each other's fixed spaces, and induct over the finite conjugate family.
Fixed spaces turn group suprema into intersections, while displacement spans
turn them into sums. Conjugation also supplies the compatible transitive
permutations. In the exceptional case, recognition identifies the distinguished
factor with the concrete Frobenius group of order 21. Transporting its order-three
subgroup proves normal generation inside that factor, and the action maps carry
the dimension-three moved space to every summand.

This is the conditional assembly part of Aschbacher–Smith E.6.24, printed p.255
(PDF p.266), citing Aschbacher, *Weak closure in finite groups of even
characteristic*, J. Algebra 70 (1981), 10.4. Existence of the local factor seed
from `Input` remains a separate theorem; no such existence is asserted here.
-/

open Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) A W)

private theorem action_inv (a : A) (v : W) : ρ a⁻¹ (ρ a v) = v := by
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem action_injective (a : A) : Function.Injective (ρ a) :=
  Function.LeftInverse.injective (action_inv ρ a)

private theorem fixedSpace_conjugate (B : Subgroup A) (a : A) :
    fixedSpace ρ (B.map (MulAut.conj a).toMonoidHom) = (fixedSpace ρ B).map (ρ a) := by
  ext v
  constructor
  · intro hv
    refine ⟨ρ a⁻¹ v, ?_, ?_⟩
    · intro b
      have hh := hv ⟨a * b * a⁻¹, b, b.property, rfl⟩
      change ρ (a * b * a⁻¹) v = v at hh
      change ρ (b : A) (ρ a⁻¹ v) = ρ a⁻¹ v
      have hh' := congrArg (ρ a⁻¹) hh
      simpa only [map_mul, Module.End.mul_apply, action_inv] using hh'
    · simpa only [inv_inv] using action_inv ρ a⁻¹ v
  · rintro ⟨w, hw, rfl⟩ ⟨b, c, hc, rfl⟩
    change ρ (a * c * a⁻¹) (ρ a w) = ρ a w
    simp only [map_mul, Module.End.mul_apply, action_inv]
    exact congrArg (ρ a) (show ρ c w = w from hw ⟨c, hc⟩)

private theorem split_conjugate {B : Subgroup A}
    (hs : IsCompl (fixedSpace ρ B) (displacementSpan ρ B ⊤)) (a : A) :
    IsCompl (fixedSpace ρ (B.map (MulAut.conj a).toMonoidHom))
      (displacementSpan ρ (B.map (MulAut.conj a).toMonoidHom) ⊤) := by
  rw [fixedSpace_conjugate, ← map_top_action ρ a, displacementSpan_conjugate]
  exact hs.map (Submodule.orderIsoMapComapOfBijective (ρ a)
    ⟨action_injective ρ a, fun v => ⟨ρ a⁻¹ v, by simpa only [inv_inv] using action_inv ρ a⁻¹ v⟩⟩)

private theorem pair_split (F M G N : Submodule (ZMod 2) W)
    (hFM : IsCompl F M) (hGN : IsCompl G N) (hMG : M ≤ G) (hNF : N ≤ F) :
    IsCompl (F ⊓ G) (M ⊔ N) := by
  apply isCompl_iff.mpr
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv hmn
    obtain ⟨m, hm, n, hn, rfl⟩ := Submodule.mem_sup.mp hmn
    have hnG : n ∈ G := by
      have := G.sub_mem hv.2 (hMG hm)
      simpa using this
    have hn0 : n = 0 := (Submodule.disjoint_def.mp hGN.disjoint) n hnG hn
    subst n
    simp only [add_zero] at hv ⊢
    exact (Submodule.disjoint_def.mp hFM.disjoint) m hv.1 hm
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    obtain ⟨f, hf, m, hm, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ F ⊔ M by rw [hFM.sup_eq_top]; trivial)
    obtain ⟨g, hg, n, hn, rfl⟩ := Submodule.mem_sup.mp
      (show f ∈ G ⊔ N by rw [hGN.sup_eq_top]; trivial)
    have hgF : g ∈ F := by
      have := F.sub_mem hf (hNF hn)
      simpa using this
    exact Submodule.mem_sup.mpr ⟨g, ⟨hgF, hg⟩, n + m,
      (M ⊔ N).add_mem ((show N ≤ M ⊔ N from le_sup_right) hn)
        ((show M ≤ M ⊔ N from le_sup_left) hm), by abel⟩

private theorem family_split {ι : Type*} [Fintype ι]
    (F M : ι → Submodule (ZMod 2) W) (hs : ∀ i, IsCompl (F i) (M i))
    (hf : ∀ i j, i ≠ j → M i ≤ F j) : IsCompl (⨅ i, F i) (⨆ i, M i) := by
  classical
  have hi (t : Finset ι) : IsCompl (⨅ i ∈ t, F i) (⨆ i ∈ t, M i) := by
    induction t using Finset.induction_on with
    | empty => simpa using (isCompl_top_bot : IsCompl (⊤ : Submodule (ZMod 2) W) ⊥)
    | @insert i t hit ih =>
      simp only [Finset.iInf_insert, Finset.iSup_insert]
      apply pair_split (F i) (M i) _ _ (hs i) ih
      · exact le_iInf fun j => le_iInf fun hj => hf i j (fun h => hit (h ▸ hj))
      · exact iSup_le fun j => iSup_le fun hj => hf j i (fun h => hit (h ▸ hj))
  simpa using hi Finset.univ

private theorem fixedSpace_iSup {ι : Type*} (B : ι → Subgroup A) :
    fixedSpace ρ (⨆ i, B i) = ⨅ i, fixedSpace ρ (B i) := by
  ext v
  constructor
  · intro hv
    exact (Submodule.mem_iInf _).mpr fun i b => hv ⟨b, le_iSup B i b.property⟩
  · intro hv b
    refine Subgroup.iSup_induction B (C := fun b => ρ b v = v) b.property ?_ ?_ ?_
    · intro i b hb
      exact ((Submodule.mem_iInf _).mp hv i) ⟨b, hb⟩
    · simp
    · intro a b ha hb
      simp only [map_mul, Module.End.mul_apply, ha, hb]

private theorem displacementSpan_iSup {ι : Type*} (B : ι → Subgroup A) :
    displacementSpan ρ (⨆ i, B i) ⊤ = ⨆ i, displacementSpan ρ (B i) ⊤ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨b, hb, v, _, rfl⟩
    have hh : ∀ v : W, ρ b v - v ∈ ⨆ i, displacementSpan ρ (B i) ⊤ := by
      refine Subgroup.iSup_induction B
        (C := fun b => ∀ v : W, ρ b v - v ∈ ⨆ i, displacementSpan ρ (B i) ⊤)
        hb ?_ ?_ ?_
      · intro i b hb v
        exact le_iSup (fun i => displacementSpan ρ (B i) ⊤) i
          (Submodule.subset_span ⟨b, hb, v, Submodule.mem_top, rfl⟩)
      · intro v
        simp
      · intro a b ha hb v
        have hh := (⨆ i, displacementSpan ρ (B i) ⊤).add_mem (ha (ρ b v)) (hb v)
        simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh
    exact hh v
  · exact iSup_le fun i => displacementSpan_mono ρ (le_iSup B i) le_rfl

private theorem global_split {ι : Type*} [Fintype ι] (B : ι → Subgroup A)
    (hs : ∀ i, IsCompl (fixedSpace ρ (B i)) (displacementSpan ρ (B i) ⊤))
    (hf : ∀ i j, i ≠ j → ∀ b ∈ B i, ∀ v ∈ displacementSpan ρ (B j) ⊤, ρ b v = v) :
    IsCompl (fixedSpace ρ (⨆ i, B i)) (displacementSpan ρ (⨆ i, B i) ⊤) := by
  rw [fixedSpace_iSup, displacementSpan_iSup]
  exact family_split _ _ hs (fun i j hij v hv b => hf j i hij.symm b b.property v hv)

private abbrev conjugate (a : A) (B : Subgroup A) : Subgroup A :=
  B.map (MulAut.conj a).toMonoidHom

private theorem conjugate_one (B : Subgroup A) : conjugate 1 B = B := by
  have hh : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
    ext x
    simp
  change B.map _ = B
  rw [hh, Subgroup.map_id]

private theorem conjugate_mul (a b : A) (B : Subgroup A) :
    conjugate a (conjugate b B) = conjugate (a * b) B := by
  change (B.map _).map _ = B.map _
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem cross_conjugate {B D : Subgroup A}
    (hf : ∀ b ∈ B, ∀ v ∈ displacementSpan ρ D ⊤, ρ b v = v) (a : A) :
    ∀ b ∈ conjugate a B, ∀ v ∈ displacementSpan ρ (conjugate a D) ⊤, ρ b v = v := by
  rintro _ ⟨b, hb, rfl⟩ v hv
  rw [← map_top_action ρ a, displacementSpan_conjugate] at hv
  obtain ⟨w, hw, rfl⟩ := hv
  change ρ (a * b * a⁻¹) (ρ a w) = ρ a w
  simp only [map_mul, Module.End.mul_apply, action_inv, hf b hb w hw]

private abbrev Conjugates (B : Subgroup A) :=
  {D : Subgroup A // ∃ a : A, conjugate a B = D}

private def conjugatesPerm (B : Subgroup A) (a : A) : Equiv.Perm (Conjugates B) where
  toFun D := ⟨conjugate a D.val, by
    obtain ⟨b, hb⟩ := D.property
    exact ⟨a * b, by rw [← hb, conjugate_mul]⟩⟩
  invFun D := ⟨conjugate a⁻¹ D.val, by
    obtain ⟨b, hb⟩ := D.property
    exact ⟨a⁻¹ * b, by rw [← hb, conjugate_mul]⟩⟩
  left_inv D := by
    apply Subtype.ext
    change conjugate a⁻¹ (conjugate a D.val) = D.val
    rw [conjugate_mul, inv_mul_cancel, conjugate_one]
  right_inv D := by
    apply Subtype.ext
    change conjugate a (conjugate a⁻¹ D.val) = D.val
    rw [conjugate_mul, mul_inv_cancel, conjugate_one]

private theorem conjugates_cross {C B : Subgroup A} (s : FactorSeed ρ C B)
    (D E : Conjugates B) (hne : D ≠ E) :
    ∀ d ∈ D.val, ∀ v ∈ displacementSpan ρ E.val ⊤, ρ d v = v := by
  obtain ⟨a, ha⟩ := D.property
  obtain ⟨b, hb⟩ := E.property
  have hprod : conjugate a (conjugate (a⁻¹ * b) B) = conjugate b B := by
    rw [conjugate_mul, mul_inv_cancel_left]
  have hd : conjugate (a⁻¹ * b) B ≠ B := by
    intro he
    apply hne
    apply Subtype.ext
    rw [← ha, ← hb, ← hprod, he]
  have hh := cross_conjugate ρ (s.cross_fixed (a⁻¹ * b) hd) a
  rw [hprod, ha, hb] at hh
  exact hh

private theorem conjugates_sup {C B : Subgroup A} (s : FactorSeed ρ C B) :
    (⨆ D : Conjugates B, D.val) = normalClosure (C : Set A) := by
  apply le_antisymm
  · apply iSup_le
    intro D
    obtain ⟨a, ha⟩ := D.property
    rw [← ha]
    rintro _ ⟨b, hb, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance b (s.in_normalClosure hb) a
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨c, hc, hcx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨a, ha⟩ := isConj_iff.mp hcx
    exact (le_iSup (fun D : Conjugates B => D.val)
      ⟨conjugate a B, a, rfl⟩) ⟨c, s.contained hc, ha⟩

private theorem exceptional_normalClosure {C B : Subgroup A} (hCB : C ≤ B)
    (hC : Nat.card C = 3) (e : B ≃* Frobenius21.Model) :
    normalClosure (C.subgroupOf B : Set B) = ⊤ := by
  let D := (C.subgroupOf B).map e.toMonoidHom
  have hD : Nat.card D = 3 := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCB).toEquiv, hC]
  have hn := Frobenius21.normalClosure_eq_top_of_card_three D hD
  apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
  rw [Subgroup.map_top_of_surjective _ e.surjective, Subgroup.map_normalClosure _ _ e.surjective]
  exact hn

/-- The distinct conjugates of a local factor seed give the complete normal-closure
factor and module decomposition. The existence of the seed is a separate hypothesis. -/
public theorem exists_decomposition_of_factorSeed [Finite A] [Finite W]
    (hfaithful : Function.Injective ρ) {C B : Subgroup A} (s : FactorSeed ρ C B) :
    Nonempty (Decomposition ρ C) := by
  classical
  let I := Conjugates B
  let : Fintype I := Fintype.ofFinite I
  let base : I := ⟨B, 1, conjugate_one B⟩
  let : Nonempty I := ⟨base⟩
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let factor : Fin (Fintype.card I) → Subgroup A := fun i => (e i).val
  let summand := fun i => displacementSpan ρ (factor i) ⊤
  have hdist : factor (e.symm base) = B := by
    dsimp [factor]
    rw [e.apply_symm_apply]
  have hgroup : (⨆ i, factor i) = normalClosure (C : Set A) := by
    rw [← conjugates_sup ρ s]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup (fun D : Conjugates B => D.val) (e i)
    · apply iSup_le
      intro D
      have hh := le_iSup factor (e.symm D)
      simpa only [factor, e.apply_symm_apply] using hh
  have hsplit : ∀ i, IsCompl (fixedSpace ρ (factor i)) (summand i) := by
    intro i
    obtain ⟨a, ha⟩ := (e i).property
    change IsCompl (fixedSpace ρ (e i).val) (displacementSpan ρ (e i).val ⊤)
    rw [← ha]
    exact split_conjugate ρ s.split a
  have hcross : ∀ i j, i ≠ j → ∀ b ∈ factor i, ∀ v ∈ summand j, ρ b v = v := by
    intro i j hij
    exact conjugates_cross ρ s (e i) (e j) (fun he => hij (e.injective he))
  refine ⟨{
    size := Fintype.card I
    positive := Fintype.card_pos
    factor := factor
    summand := summand
    distinguished := e.symm base
    contained := hdist.symm ▸ s.contained
    group_eq := hgroup
    group_independent := factors_independent_of_cross_fixed hfaithful factor hsplit hcross
    commuting := fun i j hij a ha b hb =>
      commute_of_cross_fixed hfaithful (hcross i j hij) (hcross j i hij.symm) ha hb
    split := hgroup ▸ global_split ρ factor hsplit hcross
    moved_eq := ?_
    summands_independent := summands_independent_of_cross_fixed factor hsplit hcross
    self_moved := fun i => displacementSpan_self_of_split ρ (factor i) (hsplit i)
    cross_fixed := hcross
    permuted := ?_
    transitive := ?_
    alternatives := ?_ }⟩
  · rw [← hgroup]
    exact displacementSpan_iSup ρ factor
  · intro a
    let σ : Equiv.Perm (Fin (Fintype.card I)) := (e.trans (conjugatesPerm B a)).trans e.symm
    have hh (i) : conjugate a (factor i) = factor (σ i) := by
      change conjugate a (e i).val = (e (e.symm (conjugatesPerm B a (e i)))).val
      rw [e.apply_symm_apply]
      rfl
    refine ⟨σ, fun i => ⟨hh i, ?_⟩⟩
    change (displacementSpan ρ (factor i) ⊤).map (ρ a) = displacementSpan ρ (factor (σ i)) ⊤
    rw [← displacementSpan_conjugate, map_top_action]
    exact congrArg (fun D => displacementSpan ρ D ⊤) (hh i)
  · intro i j
    obtain ⟨a, ha⟩ := (e i).property
    obtain ⟨b, hb⟩ := (e j).property
    have hh : conjugate (b * a⁻¹) (factor i) = factor j := by
      change conjugate (b * a⁻¹) (e i).val = (e j).val
      rw [← ha, conjugate_mul, inv_mul_cancel_right, hb]
    refine ⟨b * a⁻¹, hh, ?_⟩
    change (displacementSpan ρ (factor i) ⊤).map (ρ (b * a⁻¹)) = displacementSpan ρ (factor j) ⊤
    rw [← displacementSpan_conjugate, map_top_action]
    exact congrArg (fun D => displacementSpan ρ D ⊤) hh
  · rcases s.alternatives with h | ⟨hC, hB, hn, hd⟩
    · exact Or.inl (h.trans hdist.symm)
    · obtain ⟨d⟩ := Frobenius21.nonempty_mulEquiv_of_card_eq hB hn
      refine Or.inr ⟨hC, ?_, ?_, ?_⟩
      · rw [hdist]
        exact ⟨d⟩
      · rw [hdist]
        exact exceptional_normalClosure s.contained hC d
      · intro i
        obtain ⟨a, ha⟩ := (e i).property
        change Module.finrank (ZMod 2) (displacementSpan ρ (e i).val ⊤) = 3
        rw [← ha, ← map_top_action ρ a, displacementSpan_conjugate]
        exact (Submodule.equivMapOfInjective (ρ a) (action_injective ρ a)
          (displacementSpan ρ B ⊤)).finrank_eq.symm.trans hd

end Representation.RegularCyclicNormalClosure
