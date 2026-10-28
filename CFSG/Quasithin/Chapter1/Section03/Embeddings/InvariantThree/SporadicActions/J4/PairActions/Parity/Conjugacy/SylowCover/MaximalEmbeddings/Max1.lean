module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Max1.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore

/-!
# Conjugating max1 embeddings by their Sylow cores

Transport the given ambient Sylow through the supplied isomorphism, then
conjugate its literal image back to that Sylow. The two maps now induce an
automorphism of the same local Sylow. The proved characteristicity of the
literal two-core makes its two ambient images agree. Both embeddings normalize
that image. It is nontrivial and proper, so simplicity makes its normalizer
proper; maximality and equal cardinalities then identify the embeddings.

A second deduction takes ambient core-normalizer control explicitly. After the
same alignment, that control puts the given copy inside the conjugate literal
subgroup, and equal cardinalities give equality. This variant requires neither
maximality nor ambient simplicity. Both deductions avoid ambient order and
exhaustive maximal-isomorphism classification. Conjugation is `g L g⁻¹`.

Source context: Kleidman–Wilson, *The maximal subgroups of J₄* (1988),
pp.484–510; GLS3 Table 5.3i, printed p.270. The literal model comparison is
identity: all local facts concern the original ATLAS max1 word subgroup.
-/

public section

open Subgroup

private theorem exists_conjugate_core_normalized
    {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hlocal : ∀ P : Sylow 2 H,
      N ≤ P.toSubgroup ∧ (N.subgroupOf P.toSubgroup).Characteristic)
    (i : H →* G) (hi : Function.Injective i)
    (S : Sylow 2 G) (M : Subgroup G)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* H) :
    ∃ g : G, M ≤ normalizer
      (N.map ((MulAut.conj g).toMonoidHom.comp i) : Set G) := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card S := by
    change Nat.card ((S.subtype hSM).toSubgroup.map e.toMonoidHom) = Nat.card S
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv
  let T : Sylow 2 G := Sylow.ofCard (P.toSubgroup.map i) (by
    rw [card_map_of_injective hi, hcard, S.card_eq_multiplicity])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let j : H →* G := (MulAut.conj g).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hi
  have hPS : P.toSubgroup.map j = S.toSubgroup := by
    change P.toSubgroup.map ((MulAut.conj g).toMonoidHom.comp i) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hjS (p : P) : j p ∈ S := by
    change j p ∈ S.toSubgroup
    rw [← hPS]
    exact mem_map_of_mem j p.property
  let m : P →* M := (j.comp P.toSubgroup.subtype).codRestrict M
    (fun p => hSM (hjS p))
  let uHom : P →* P := (e.toMonoidHom.comp m).codRestrict P.toSubgroup (by
    intro p
    exact mem_map_of_mem e.toMonoidHom (hjS p))
  have hu : Function.Injective uHom := by
    intro a b hab
    apply Subtype.ext
    apply hj
    exact congrArg Subtype.val (e.injective (congrArg Subtype.val hab))
  let u : P ≃* P := MulEquiv.ofBijective uHom
    ⟨hu, Finite.surjective_of_injective hu⟩
  have hNK : N.map j ≤ (N.comap e.toMonoidHom).map M.subtype := by
    rintro _ ⟨n, hn, rfl⟩
    let p : P := ⟨n, (hlocal P).1 hn⟩
    have hp : u p ∈ N.subgroupOf P.toSubgroup :=
      (characteristic_iff_le_comap.mp (hlocal P).2 u) hn
    exact ⟨m p, hp, rfl⟩
  have hKcard : Nat.card (N.comap e.toMonoidHom) = Nat.card N := by
    have he : (N.comap e.toMonoidHom).map e.toMonoidHom = N :=
      map_comap_eq_self_of_surjective e.surjective N
    exact (card_map_of_injective e.injective).symm.trans
      (congrArg (fun K : Subgroup H => Nat.card K) he)
  have hNK_eq : N.map j = (N.comap e.toMonoidHom).map M.subtype := by
    apply eq_of_le_of_card_ge hNK
    rw [card_map_of_injective hj, card_map_of_injective M.subtype_injective, hKcard]
  have hMN : M ≤ normalizer (N.map j : Set G) := by
    rw [hNK_eq]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (N.comap e.toMonoidHom).le_normalizer_map M.subtype
  exact ⟨g, hMN⟩

private theorem conjugate_range_of_characteristic_sylow_subgroup
    {G H : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hne : N ≠ ⊥) (hproper : N ≠ ⊤)
    (hlocal : ∀ P : Sylow 2 H,
      N ≤ P.toSubgroup ∧ (N.subgroupOf P.toSubgroup).Characteristic)
    (i : H →* G) (hi : Function.Injective i)
    (S : Sylow 2 G) (M : Subgroup G) (hM : IsCoatom M)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* H) :
    ∃ g : G, M = i.range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hMN⟩ := exists_conjugate_core_normalized N hlocal i hi S M hSM e
  let j : H →* G := (MulAut.conj g).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hi
  have hNbot : N.map j ≠ ⊥ := fun h =>
    hne ((N.map_eq_bot_iff_of_injective hj).mp h)
  have hNtop : N.map j ≠ ⊤ := by
    intro h
    apply hproper
    apply top_unique
    intro n _
    have hn : j n ∈ N.map j := h ▸ mem_top _
    obtain ⟨n', hn', he⟩ := hn
    exact hj he ▸ hn'
  have hnormalizer : normalizer (N.map j : Set G) ≠ ⊤ := by
    intro h
    have hn : (N.map j).Normal := normalizer_eq_top_iff.mp h
    exact hn.eq_bot_or_eq_top.elim hNbot hNtop
  have hNM : normalizer (N.map j : Set G) = M :=
    (hM.le_iff_eq hnormalizer).mp hMN
  have hjM : j.range ≤ M := by
    rw [← hNM]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using
      N.le_normalizer_map j
  have heq : M = j.range := by
    symm
    apply eq_of_le_of_card_ge hjM
    exact le_of_eq ((Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv))
  refine ⟨g, ?_⟩
  simpa only [j, MonoidHom.range_comp] using heq

private theorem conjugate_range_of_core_normalizer
    {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hlocal : ∀ P : Sylow 2 H,
      N ≤ P.toSubgroup ∧ (N.subgroupOf P.toSubgroup).Characteristic)
    (i : H →* G) (hi : Function.Injective i)
    (hN : normalizer (N.map i : Set G) ≤ i.range)
    (S : Sylow 2 G) (M : Subgroup G)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* H) :
    ∃ g : G, M = i.range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hMN⟩ := exists_conjugate_core_normalized N hlocal i hi S M hSM e
  let j : H →* G := (MulAut.conj g).toMonoidHom.comp i
  have hj : Function.Injective j := (MulAut.conj g).injective.comp hi
  have hNj : normalizer (N.map j : Set G) ≤ j.range := by
    change normalizer (N.map ((MulAut.conj g).toMonoidHom.comp i) : Set G) ≤ _
    rw [← map_map, ← map_equiv_normalizer_eq, MonoidHom.range_comp]
    exact map_mono hN
  have heq : M = j.range := by
    apply eq_of_le_of_card_ge (hMN.trans hNj)
    exact le_of_eq (((Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv)).symm)
  refine ⟨g, ?_⟩
  simpa only [j, MonoidHom.range_comp] using heq

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

open Janko4 Janko4.Cardinality

attribute [local irreducible] max1Subgroup localKernel

/-- Characteristicity of the literal two-core inside its Sylow subgroups
suffices for the required ambient embedding comparison. This conditional
interface is retained alongside its unconditional specialization below. -/
theorem max1MaximalEmbeddingConjugacy_of_sylowCoreCharacteristic
    (hchar : Max1SylowCoreCharacteristic) : MaximalEmbeddingConjugacyAt
      (max1Subgroup matrixA_mul_self matrixB_pow_four) := by
  intro _ _ _ S M hM hSM he
  obtain ⟨e⟩ := he
  have hproper : localKernel matrixA_mul_self matrixB_pow_four ≠ ⊤ := by
    intro h
    have hc := localKernel_card matrixA_mul_self matrixB_pow_four
    rw [h, card_top, max1Subgroup_card] at hc
    norm_num at hc
  have hp : IsPGroup 2 (localKernel matrixA_mul_self matrixB_pow_four) :=
    IsPGroup.of_card (n := 11) (localKernel_card matrixA_mul_self matrixB_pow_four)
  obtain ⟨g, hg⟩ := conjugate_range_of_characteristic_sylow_subgroup
    (localKernel matrixA_mul_self matrixB_pow_four)
    (LocalStructure.localKernel_ne_bot _ _) hproper
    (fun P => ⟨hp.le_sylow_of_normal P, hchar P⟩)
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype_injective
    S M hM hSM e
  exact ⟨g, by simpa only [range_subtype] using hg⟩

/-- Every maximal overgroup of an ambient Sylow that is isomorphic to the literal
max1 subgroup is an ambient conjugate of that subgroup. -/
theorem max1MaximalEmbeddingConjugacy : MaximalEmbeddingConjugacyAt
    (max1Subgroup matrixA_mul_self matrixB_pow_four) :=
  max1MaximalEmbeddingConjugacy_of_sylowCoreCharacteristic
    LocalStructure.localKernel_sylow_characteristic

/-- Core-normalizer control conjugates any isomorphic copy containing an ambient
Sylow. Neither maximality of that copy nor simplicity of the ambient group is
required. The ambient normalizer premise is explicit. -/
theorem max1CopyConjugacy_of_coreNormalizer
    (hN : normalizer
      ((localKernel matrixA_mul_self matrixB_pow_four).map
        (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype : Set Model) ≤
      max1Subgroup matrixA_mul_self matrixB_pow_four)
    (S : Sylow 2 Model) (M : Subgroup Model) (hSM : S.toSubgroup ≤ M)
    (e : M ≃* max1Subgroup matrixA_mul_self matrixB_pow_four) :
    ∃ g : Model, M = (max1Subgroup matrixA_mul_self matrixB_pow_four).map
      (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := conjugate_range_of_core_normalizer
    (localKernel matrixA_mul_self matrixB_pow_four)
    (fun P => ⟨LocalStructure.localKernel_le_sylow P,
      LocalStructure.localKernel_sylow_characteristic P⟩)
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype
    (max1Subgroup matrixA_mul_self matrixB_pow_four).subtype_injective
    (by simpa only [range_subtype] using hN) S M hSM e
  exact ⟨g, by simpa only [range_subtype] using hg⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
