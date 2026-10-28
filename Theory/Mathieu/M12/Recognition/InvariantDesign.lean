module

public import Theory.Mathieu.M11.SharpLocalOrbits
public import Theory.GroupTheory.SteinerSystemOrbit
public import Mathlib.Algebra.Group.Action.TransferInstance
public import Mathlib.GroupTheory.Index

/-!
# Invariant hexads from a sharply five-transitive degree-twelve action

A point stabilizer acts sharply four-transitively on the other eleven points.
Its four-set stabilizer is transitive on six of the seven remaining points,
by the existing degree-eleven local-orbit theorem. Adjoining the distinguished
point produces a five-set with the same local transitivity property. The group
cannot be transitive on all six-sets, since 924 does not divide its order 95040.
The orbit construction therefore gives an invariant Steiner system `S(5,6,12)`.

Source: the recognition step in Aschbacher, *A 2-local characterization of M12*,
Illinois J. Math. 47 (2003), Lemma 4.11, and *Sporadic Groups*, Exercise 6.6.7.
The local ingredient is the degree-eleven argument used in M11 recognition.
-/

open scoped Pointwise

namespace Sporadic.Mathieu

/-- Sharp five-transitivity on twelve points forces order 95040. -/
public theorem sharpFive_degreeTwelve_card
    {G : Type*} [Group G] [MulAction G (Fin 12)]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5) :
    Nat.card G = 95040 := by
  have hc := h.natCard_eq_descFactorial (Fin.castLEEmb (by decide : 5 ≤ 12))
  norm_num [Nat.descFactorial] at hc
  exact hc

/-- The six-subsets cannot form a single orbit in a sharp degree-twelve action. -/
public theorem sharpFive_degreeTwelve_not_sixHomogeneous
    {G : Type*} [Group G] [MulAction G (Fin 12)]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5) :
    ¬ (∀ B : Finset (Fin 12), B.card = 6 →
      ∀ C : Finset (Fin 12), C.card = 6 → ∃ g : G, g • B = C) := by
  classical
  intro ht
  let B : Finset (Fin 12) := Finset.univ.map (Fin.castLEEmb (by decide : 6 ≤ 12))
  have hB : B.card = 6 := by simp [B]
  have horbit : MulAction.orbit G B =
      ((Finset.univ : Finset (Fin 12)).powersetCard 6 : Set (Finset (Fin 12))) := by
    ext C
    simp only [Finset.mem_coe, Finset.mem_powersetCard_univ]
    constructor
    · rintro ⟨g, rfl⟩
      simpa only [Finset.card_smul_finset] using hB
    · intro hC
      exact ht B hB C hC
  have hdvd := (MulAction.stabilizer G B).index_dvd_card
  rw [MulAction.index_stabilizer, horbit, Set.ncard_coe_finset,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    sharpFive_degreeTwelve_card h] at hdvd
  norm_num [Nat.choose] at hdvd

private theorem sharp_stabilizer_transport
    {G α Y : Type*} [Group G] [MulAction G α] {n : ℕ}
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G α (n + 1))
    (a : α) (e : Y ≃ SubMulAction.ofStabilizer G a) (base : Fin n ↪ Y) :
    let _ := e.mulAction (MulAction.stabilizer G a)
    Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive
      (MulAction.stabilizer G a) Y n := by
  dsimp only
  let _ := e.mulAction (MulAction.stabilizer G a)
  have htransport (x y : Fin n ↪ Y) :
      ∃! g : MulAction.stabilizer G a, g • x = y := by
    let x' := x.trans e.toEmbedding
    let y' := y.trans e.toEmbedding
    obtain ⟨g, hgxy, hu⟩ := h.existsUnique_smul_eq
      (SubMulAction.ofStabilizer.snoc x') (SubMulAction.ofStabilizer.snoc y')
    have hg : g ∈ MulAction.stabilizer G a := by
      rw [MulAction.mem_stabilizer_iff]
      have he := congrArg (fun z : Fin (n + 1) ↪ α => z (Fin.last n)) hgxy
      simpa only [Function.Embedding.smul_apply, SubMulAction.ofStabilizer.snoc_last] using he
    have hxy : (⟨g, hg⟩ : MulAction.stabilizer G a) • x' = y' := by
      ext i
      have he := congrArg (fun z : Fin (n + 1) ↪ α => z i.castSucc) hgxy
      simpa only [Function.Embedding.smul_apply, SubMulAction.ofStabilizer.snoc_castSucc,
        SubMulAction.val_smul_of_tower, Subgroup.smul_def] using he
    refine ⟨⟨g, hg⟩, ?_, ?_⟩
    · apply Function.Embedding.ext
      intro i
      apply e.injective
      have hi := congrArg (fun z : Fin n ↪ SubMulAction.ofStabilizer G a => z i) hxy
      simpa [Equiv.smul_def, x', y'] using hi
    · intro k hk
      have hk' : k • x' = y' := by
        apply Function.Embedding.ext
        intro i
        have hi := congrArg (fun z : Fin n ↪ Y => e (z i)) hk
        simpa [Equiv.smul_def, x', y'] using hi
      apply Subtype.ext
      apply hu k
      ext i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
      · have he := congrArg (fun z : Fin n ↪ SubMulAction.ofStabilizer G a =>
          (z i : α)) hk'
        simpa only [Function.Embedding.smul_apply, SubMulAction.ofStabilizer.snoc_castSucc,
          SubMulAction.val_smul_of_tower, Subgroup.smul_def] using he
      · simpa only [Function.Embedding.smul_apply, SubMulAction.ofStabilizer.snoc_last] using
          (MulAction.mem_stabilizer_iff.mp k.property)
  apply Theory.GroupTheory.MulAction.isSharplyMultiplyPretransitive_of_bijective_orbitMap base
  constructor
  · intro g k hgk
    obtain ⟨u, _, hu⟩ := htransport base (g • base)
    exact (hu g rfl).trans (hu k hgk.symm).symm
  · intro y
    exact (htransport base y).exists

/-- Every finite faithful sharply five-transitive degree-twelve action preserves
a Steiner system `S(5,6,12)`. -/
public theorem sharpFive_degreeTwelve_exists_invariantDesign
    {G : Type*} [Group G] [Finite G] [MulAction G (Fin 12)]
    [FaithfulSMul G (Fin 12)]
    (h : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive G (Fin 12) 5) :
    ∃ D : Theory.GroupTheory.SteinerSystem (Fin 12) 5 6,
      ∀ g : G, MulAction.toPerm g ∈ D.aut := by
  classical
  let a : Fin 12 := 0
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  have hX : Fintype.card X = 11 := by
    rw [← Nat.card_eq_fintype_card, SubMulAction.nat_card_ofStabilizer_eq]
    simp
  let e : Fin 11 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  let _ : MulAction H (Fin 11) := e.mulAction H
  have h4 : Theory.GroupTheory.MulAction.IsSharplyMultiplyPretransitive H (Fin 11) 4 :=
    sharp_stabilizer_transport h a e (Fin.castLEEmb (by decide : 4 ≤ 11))
  let _ : FaithfulSMul H (Fin 11) := ⟨by
    intro g k hsame
    apply (h4.bijective_orbitMap (Fin.castLEEmb (by decide : 4 ≤ 11))).injective
    apply Function.Embedding.ext
    intro i
    exact hsame _⟩
  let s : Finset (Fin 11) := Finset.univ.map (Fin.castLEEmb (by decide : 4 ≤ 11))
  have hs : s.card = 4 := by simp [s]
  obtain ⟨p, hp, _, hlocal⟩ :=
    h4.exists_fixed_point_and_transitive_fourSet_complement s hs
  let f : Fin 11 ↪ Fin 12 := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hfa (i : Fin 11) : f i ≠ a := (e i).property
  have hf (g : H) (i : Fin 11) : f (g • i) = (g : G) • f i := by
    change (e (e.symm (g • e i)) : Fin 12) = (g : G) • (e i : Fin 12)
    simp [Subgroup.smul_def]
  let S : Finset (Fin 12) := insert a (s.map f)
  have ha : a ∉ s.map f := by
    simp only [Finset.mem_map, not_exists, not_and]
    exact fun i _ hi => hfa i hi
  have hS : S.card = 5 := by simp [S, ha, hs]
  have hpS : f p ∉ S := by
    simp [S, hfa, hp]
  apply Theory.GroupTheory.SteinerSystem.exists_invariant_of_two_extension_orbits
    5 h.isMultiplyPretransitive (sharpFive_degreeTwelve_not_sixHomogeneous h)
    S (f p) hS hpS
  intro q hq hqp r hr hrp
  have hqa : q ≠ a := fun he => hq (by simp [S, he])
  have hra : r ≠ a := fun he => hr (by simp [S, he])
  let q' : Fin 11 := e.symm ⟨q, hqa⟩
  let r' : Fin 11 := e.symm ⟨r, hra⟩
  have hq' : f q' = q := by simp [f, q']
  have hr' : f r' = r := by simp [f, r']
  have hq's : q' ∉ s := by
    intro hmem
    apply hq
    exact Finset.mem_insert_of_mem (hq' ▸ Finset.mem_map.mpr ⟨q', hmem, rfl⟩)
  have hr's : r' ∉ s := by
    intro hmem
    apply hr
    exact Finset.mem_insert_of_mem (hr' ▸ Finset.mem_map.mpr ⟨r', hmem, rfl⟩)
  obtain ⟨g, hgs, hgqr⟩ := hlocal q' hq's
    (fun he => hqp (hq'.symm.trans (congrArg f he))) r' hr's
    (fun he => hrp (hr'.symm.trans (congrArg f he)))
  refine ⟨g, ?_, ?_⟩
  · have hmap : (g : G) • s.map f = (g • s).map f := by
      ext x
      simp only [Finset.mem_smul_finset, Finset.mem_map]
      constructor
      · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨g • i, ⟨i, hi, rfl⟩, hf g i⟩
      · rintro ⟨j, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨f i, ⟨i, hi, rfl⟩, (hf g i).symm⟩
    change (g : G) • insert a (s.map f) = insert a (s.map f)
    rw [Finset.smul_finset_insert, g.property, hmap, hgs]
  · rw [← hq', ← hf, hgqr, hr']

end Sporadic.Mathieu
