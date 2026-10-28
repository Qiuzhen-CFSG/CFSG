module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Parity.Conjugacy.SylowCover.MaximalEmbeddings.Reduction

/-!
# A local characteristic-subgroup route to the max4 embedding comparison

Suppose the literal max4 subgroup has a nontrivial normal two-subgroup A
whose restriction to each local Sylow subgroup is characteristic. Given an
isomorphic maximal Sylow overgroup, transport its Sylow to max4 and conjugate
that Sylow back in the ambient group. The composite of the two comparisons
is an automorphism of the local Sylow, so it preserves A. Both embeddings
therefore normalize the same nontrivial subgroup. Simplicity makes its
normalizer proper, and maximality and equal orders identify the embeddings.

The exported theorem is conditional: constructing A and proving its local
characteristicity for the literal ATLAS word subgroup is still required.
Neither the proposed quotient S₅ × L₃(2) nor an ambient order calculation is
used. The map convention throughout is g L g⁻¹.

Source context: Kleidman--Wilson, *The maximal subgroups of J₄*, Proc. London
Math. Soc. 56 (1988), 484--510; the Sylow-overgroup application cited as
[Asc86b] in Aschbacher--Smith, printed p.511/PDF p.528 of `refs/quasithin.pdf`.
The normalizer argument below is general finite-group theory; the source
context does not supply the outstanding concrete characteristicity proof.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover

/-- A normal subgroup characteristic in local Sylows aligns maximal embeddings. -/
private theorem conjugate_of_sylow_characteristic_normal
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime] (L : Subgroup G) (A : Subgroup L) [A.Normal]
    (hA : A ≠ ⊥) (hAp : IsPGroup p A)
    (hchar : ∀ P : Sylow p L, (A.subgroupOf P.toSubgroup).Characteristic)
    (S : Sylow p G) (M : Subgroup G) (hM : IsCoatom M)
    (hSM : S.toSubgroup ≤ M) (e : M ≃* L) :
    ∃ g : G, M = L.map (MulAut.conj g).toMonoidHom := by
  let P := (S.subtype hSM).mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card S := by
    change Nat.card ((S.subtype hSM).toSubgroup.map e.toMonoidHom) = Nat.card S
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv
  let T : Sylow p G := Sylow.ofCard (P.toSubgroup.map L.subtype) (by
    rw [card_map_of_injective L.subtype_injective, hcard, S.card_eq_multiplicity])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  let j : L →* G := (MulAut.conj g).toMonoidHom.comp L.subtype
  have hj : Function.Injective j := (MulAut.conj g).injective.comp L.subtype_injective
  have hPS : P.toSubgroup.map j = S.toSubgroup := by
    change P.toSubgroup.map ((MulAut.conj g).toMonoidHom.comp L.subtype) = _
    rw [← map_map]
    exact congrArg Sylow.toSubgroup hg
  have hjS (x : P) : j x ∈ S.toSubgroup := by
    rw [← hPS]
    exact mem_map_of_mem j x.property
  let u : P →* M := (j.comp P.toSubgroup.subtype).codRestrict M (fun x => hSM (hjS x))
  let v : P →* L := e.toMonoidHom.comp u
  have hvP (x : P) : v x ∈ P.toSubgroup := by
    exact mem_map_of_mem e.toMonoidHom (hjS x)
  let alpha : P →* P := v.codRestrict P.toSubgroup hvP
  have halpha : Function.Injective alpha := by
    intro x y h
    apply Subtype.ext
    apply hj
    have h' : e (u x) = e (u y) := congrArg Subtype.val h
    exact congrArg Subtype.val (e.injective h')
  let f : P ≃* P := MulEquiv.ofBijective alpha ⟨halpha, Finite.surjective_of_injective halpha⟩
  let k : L →* G := M.subtype.comp e.symm.toMonoidHom
  have hk : Function.Injective k := M.subtype_injective.comp e.symm.injective
  have hkM : k.range = M := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  let B : Subgroup G := A.map k
  have hAB : A.map j ≤ B := by
    rintro _ ⟨a, ha, rfl⟩
    let a' : P := ⟨a, hAp.le_sylow_of_normal P ha⟩
    have hfA : f a' ∈ A.subgroupOf P.toSubgroup :=
      characteristic_iff_le_comap.mp (hchar P) f ha
    refine ⟨v a', hfA, ?_⟩
    change (e.symm (e (u a')) : G) = j a
    rw [e.symm_apply_apply]
    rfl
  have hABeq : A.map j = B := by
    apply eq_of_le_of_card_ge hAB
    change Nat.card (A.map k) ≤ Nat.card (A.map j)
    rw [card_map_of_injective hk, card_map_of_injective hj]
  have hMN : M ≤ normalizer (B : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, hkM] using A.le_normalizer_map k
  have hBne : B ≠ ⊥ := fun h => hA ((A.map_eq_bot_iff_of_injective hk).mp h)
  have hBM : B ≤ M := by
    rw [← hkM]
    exact map_le_range _ _
  have hN : normalizer (B : Set G) ≠ ⊤ := by
    intro hn
    rcases (normalizer_eq_top_iff.mp hn).eq_bot_or_eq_top with hb | hb
    · exact hBne hb
    · exact hM.ne_top (top_unique (hb ▸ hBM))
  have hNM : normalizer (B : Set G) = M := (hM.le_iff.mp hMN).resolve_left hN
  have hjM : j.range ≤ M := by
    rw [← hNM, ← hABeq]
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map] using A.le_normalizer_map j
  have hMeq : M = j.range := by
    symm
    apply eq_of_le_of_card_ge hjM
    exact le_of_eq ((Nat.card_congr e.toEquiv).trans
      (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv))
  refine ⟨g, ?_⟩
  simpa only [j, MonoidHom.range_comp, range_subtype] using hMeq

/-- A precise intrinsic model input for the max4 branch. Normality is inside
max4, and characteristicity is inside its Sylow subgroups. This proposition
asserts no quotient identification or ambient conjugacy. -/
@[expose] def Max4SylowCharacteristicNormal : Prop :=
  ∃ A : Subgroup Janko4.LocalStructure.SymmetricLinear.max4Subgroup,
    A.Normal ∧ A ≠ ⊥ ∧ IsPGroup 2 A ∧
      ∀ P : Sylow 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup,
        (A.subgroupOf P.toSubgroup).Characteristic

/-- The normalizer comparison reduces the max4 branch to the displayed
intrinsic model input. Final assembly must construct that input. -/
theorem max4MaximalEmbeddingConjugacy_of_sylowCharacteristicNormal
    (hlocal : Max4SylowCharacteristicNormal) :
    MaximalEmbeddingConjugacyAt Janko4.LocalStructure.SymmetricLinear.max4Subgroup := by
  intro _ _ _ S M hM hSM he
  obtain ⟨A, hAnormal, hA, hAp, hchar⟩ := hlocal
  let := hAnormal
  obtain ⟨e⟩ := he
  exact conjugate_of_sylow_characteristic_normal _ A hA hAp hchar S M hM hSM e

/-- The literal max4 subgroup has a normal elementary subgroup of order eight.
This is an intrinsic matrix-group assertion, with normality relative to max4. -/
@[expose] def Max4NormalElementaryEight : Prop :=
  ∃ A : Subgroup Janko4.LocalStructure.SymmetricLinear.max4Subgroup,
    A.Normal ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 8

/-- Intrinsic rigidity of the local Sylow groups: their normal elementary
subgroups of order eight are characteristic. This assertion contains no
ambient embedding comparison or maximal-subgroup classification. -/
@[expose] def Max4SylowElementaryEightCharacteristic : Prop :=
  ∀ P : Sylow 2 Janko4.LocalStructure.SymmetricLinear.max4Subgroup,
    ∀ A : Subgroup P, A.Normal → IsElementaryAbelian 2 A → Nat.card A = 8 →
      A.Characteristic

/-- The two independent local facts supply the subgroup needed by the
normalizer argument. The same normal elementary group lies in every Sylow;
restriction preserves its normality, elementary structure and order. -/
theorem max4SylowCharacteristicNormal_of_normalElementaryEight
    (hA : Max4NormalElementaryEight)
    (hS : Max4SylowElementaryEightCharacteristic) :
    Max4SylowCharacteristicNormal := by
  obtain ⟨A, hnormal, habelian, hcard⟩ := hA
  let := hnormal
  let := habelian
  have hAp := IsElementaryAbelian.isPGroup 2 A
  refine ⟨A, hnormal, ?_, hAp, ?_⟩
  · intro h
    rw [h, card_bot] at hcard
    norm_num at hcard
  · intro P
    have hle := hAp.le_sylow_of_normal P
    apply hS P (A.subgroupOf P.toSubgroup) inferInstance
      (IsElementaryAbelian.subgroupOf hle)
    exact (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hcard

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Max4Conjugacy.SylowCover
