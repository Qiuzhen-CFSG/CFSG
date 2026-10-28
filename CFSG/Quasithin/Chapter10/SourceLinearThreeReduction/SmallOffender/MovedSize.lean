module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Preparation
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureLowerBound

/-!
# Nonfixed normalizing elements at corank at most one

Perfectness bounds the literal moved factor modulo its full component-fixed
subgroup by at least eight, without an A₅ or linear-three marking. Otherwise
the quotient action has solvable permutation image and is trivial, and the
three-subgroups lemma makes the original moved factor trivial.

The two-factor action of M bounds a factor-normalizer index by two. An
offender of corank at most one therefore meets that normalizer outside the
conjugated component-fixed subgroup. This supplies the element b used in
the corank-one branch of Aschbacher--Smith 10.2.12, printed pp.754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original moved factor modulo its full fixed subgroup has order at
least eight. No irreducibility or choice of module model is required. -/
theorem moved_fixed_quotient_card_ge_eight :
    8 ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ := by
  classical
  let W := ⁅D.fullModule,L⁆
  let C := centralizer (L : Set G)
  let := source_full_moved_elementary D
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : (C.subgroupOf W).Normal := inferInstance
  have hLW : L ≤ normalizer (W : Set G) := normalizer_commutator_ge_right _ _
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action L W C hLW
    ((le_centralizer_iff.mpr (le_rfl : C ≤ centralizer (L : Set G))).trans
      (centralizer_le_normalizer (C : Set G))) inferInstance
  have hn : ρ ≠ 1 := by
    intro he
    have hc : ⁅W,L⁆ ≤ C := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl w hw
      have hh := hρ ⟨l,hl⟩ ⟨w,hw⟩
      rw [he] at hh
      have hi := QuotientGroup.eq_iff_div_mem.mp hh.symm
      change l * w * l⁻¹ / w ∈ C at hi
      simpa only [commutatorElement_def, div_eq_mul_inv] using hi
    have hz : ⁅W,L⁆ = ⊥ := commutator_eq_bot_of_iterated_eq_bot W L
      (commutator_eq_bot_iff_le_centralizer.mpr hc)
    exact source_full_moved_ne_bot D
      (commutator_eq_bot_of_iterated_eq_bot D.fullModule L hz)
  let Q := W ⧸ C.subgroupOf W
  have hQ : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 W).of_surjective
    (QuotientGroup.mk' (C.subgroupOf W)) (QuotientGroup.mk'_surjective _)
  change 8 ≤ Nat.card Q
  by_contra hsmall
  obtain ⟨n,hnQ⟩ := hQ.exists_card_eq
  have hnlt : n < 3 := by
    by_contra hge
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt hge)
    rw [← hnQ] at hh
    exact hsmall hh
  have hfour : Nat.card Q ≤ 4 := by
    rw [hnQ]
    exact Nat.pow_le_pow_right (by decide) (by omega : n ≤ 2)
  let : Fintype Q := Fintype.ofFinite Q
  let e : Q ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le
    (show Fintype.card Q ≤ Fintype.card (Fin 4) by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using hfour))
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm Q) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  let f : L →* Equiv.Perm Q := (MulAction.toPermHom (MulAut Q) Q).comp ρ
  let := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hnontrivial
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  apply hn
  ext l q
  have hf : f l = 1 := congrArg Subtype.val
    (Subsingleton.elim (f.rangeRestrict l) 1)
  exact congrArg (fun p : Equiv.Perm Q => p q) hf

/-- The actual corank-one intersection contains a nonfixed element which
normalizes the original moved factor, as required on p.754. -/
theorem corank_one_exists_noncentral_normalizing_element
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {g : G} (hsmall : subgroupCorank
      (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1) :
    ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom,
      b ∈ D.maximalLocal ∧ b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
      b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  let A := W ⊓ D.maximalLocal
  let N := normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let B := A ⊓ N
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hidx (P Q : Subgroup G) : P.relIndex Q ≠ 0 := by
    change Nat.card (Q ⧸ P.subgroupOf Q) ≠ 0
    exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ V := map_mono (le_normalizer_iff_commutator_le_left.mp hLV)
  have hMV : D.maximalLocal.relIndex V ≤ 2 := by
    have he : D.maximalLocal.relIndex V = 2 ^ subgroupCorank V (V ⊓ D.maximalLocal) := by
      rw [subgroupCorank_eq_quotient_finrank, relIndex_eq_two_pow_quotient_finrank V D.maximalLocal]
      congr 1
      rw [inf_subgroupOf_left]
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hsmall
  have hAW : A.relIndex W ≤ 2 := by
    rw [show A = W ⊓ D.maximalLocal from rfl, inf_relIndex_left]
    exact (relIndex_le_of_le_right hWV (hidx _ _)).trans hMV
  have hBA : B.relIndex A ≤ 2 := by
    rw [show B = A ⊓ N from rfl, inf_relIndex_left]
    exact source_nonnormal_moved_normalizer_index_le_two D hn inf_le_right
  have hBW : B.relIndex W ≤ 4 := by
    rw [← relIndex_mul_relIndex B A W inf_le_left inf_le_left]
    exact Nat.mul_le_mul hBA hAW
  have hCW : 8 ≤ C.relIndex W := by
    change 8 ≤ (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    rw [← Theory.Quasithin.map_centralizer (MulAut.conj g) L,
      relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact moved_fixed_quotient_card_ge_eight D
  have hnBC : ¬ B ≤ C := by
    intro hBC
    have hi := relIndex_le_of_le_left hBC (hidx B W)
    omega
  obtain ⟨b,hb,hbc⟩ := Set.not_subset.mp hnBC
  exact ⟨b,hb.1.1,hb.1.2,hb.2,hbc⟩

end CFSG.Quasithin.Chapter10.SmallOffender
