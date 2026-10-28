module

public import Theory.Mathieu.M12.A5Fixer.Inputs
public import Theory.Mathieu.M12.Properties.Transitivity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.SharpSetStabilizer

/-!
# Inner centralizers of A₅ subgroups of M₁₂

For a moved point `x`, its stabilizer `H` in an embedded A₅ is nontrivial
and proper: an orbit with trivial stabilizer would have sixty points.
The set of points with stabilizer exactly `H` is a block. Its setwise
stabilizer lies in the proper normalizer of `H`, so simplicity and the
coset action force at least five disjoint translates. Thus this set has
at most two points in the natural degree-twelve action.

Evaluation at `x` maps the centralizer into this set injectively. Indeed,
an element in its kernel fixes the A₅-orbit of `x`, which has at least
five points, and sharp five-transitivity makes it the identity.

This proves the inner calculation used in the M₁₂ case of
Aschbacher–Smith 16.3.5, in the setting of 16.1.5(4) and 16.1.7(3f)
(combined manuscript of 1 March 2004, printed pp.1171–1173 and 1178–1179).
The carrier and action are the actual Witt-design automorphism group;
no involution table or subgroup-conjugacy catalogue is required.
-/

open Subgroup MulAction
open scoped Pointwise

namespace Sporadic.Mathieu.M12A5Fixer

private theorem block_count {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (B : Set X) (hB : IsBlock G B) :
    (stabilizer G B).index * B.ncard ≤ Nat.card X := by
  classical
  let rep : orbit G B → G := fun A => Classical.choose A.property
  have hrep (A : orbit G B) : rep A • B = A := Classical.choose_spec A.property
  let f : (orbit G B) × B → X := fun z => rep z.1 • z.2.val
  have hf : Function.Injective f := by
    rintro ⟨A, a⟩ ⟨D, d⟩ he
    have hAD : rep A • B = rep D • B := by
      apply hB.smul_eq_smul_of_nonempty
      refine ⟨f (A, a), Set.smul_mem_smul_set a.property, ?_⟩
      rw [he]
      exact Set.smul_mem_smul_set d.property
    have hAD' : A = D := Subtype.ext ((hrep A).symm.trans (hAD.trans (hrep D)))
    subst D
    have had : a = d := Subtype.ext (MulAction.injective (rep A) he)
    subst d
    rfl
  simpa only [Nat.card_prod, Nat.card_coe_set_eq, index_stabilizer] using
    Nat.card_le_card_of_injective f hf

private theorem stabilizer_fiber_smul {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) (g : G) :
    g • {x : X | stabilizer G x = H} =
      {x : X | stabilizer G x = H.map (MulAut.conj g).toMonoidHom} := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change stabilizer G y = H at hy
    change stabilizer G (g • y) = _
    rw [stabilizer_smul_eq_stabilizer_map_conj, hy]
  · intro hx
    change stabilizer G x = H.map (MulAut.conj g).toMonoidHom at hx
    refine ⟨g⁻¹ • x, ?_, by simp⟩
    apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective
    simpa only [← stabilizer_smul_eq_stabilizer_map_conj, smul_inv_smul] using hx

private theorem stabilizer_fiber_block {G X : Type*} [Group G] [MulAction G X]
    (H : Subgroup G) : IsBlock G {x : X | stabilizer G x = H} := by
  apply isBlock_iff_smul_eq_smul_of_nonempty.mpr
  intro g h ⟨x, hx, hx'⟩
  rw [stabilizer_fiber_smul] at hx hx' ⊢
  rw [stabilizer_fiber_smul, ← hx, ← hx']

private theorem small_index {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hc : Nat.card G = 60) (H : Subgroup G) (hH : H ≠ ⊤) : 5 ≤ H.index := by
  by_contra hn
  apply hH
  apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
  have hb := Nat.factorial_le (show H.index ≤ 4 by omega)
  rw [hc]
  norm_num [Nat.factorial] at hb ⊢
  omega

private theorem stabilizer_fiber_card {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] [MulAction G (Fin 12)] (hc : Nat.card G = 60)
    (x : Fin 12) (hproper : stabilizer G x ≠ ⊤) :
    {y : Fin 12 | stabilizer G y = stabilizer G x}.ncard ≤ 2 := by
  let H := stabilizer G x
  let B : Set (Fin 12) := {y | stabilizer G y = H}
  have hHbot : H ≠ ⊥ := by
    intro hb
    have hi := index_stabilizer G x
    change H.index = _ at hi
    rw [hb, index_bot, hc] at hi
    have hn := (orbit G x).ncard_le_card
    norm_num at hn
    omega
  have hn : normalizer (H : Set G) ≠ ⊤ := by
    intro h
    exact ((normalizer_eq_top_iff.mp h).eq_bot_or_eq_top).elim hHbot hproper
  have hBN : stabilizer G B ≤ normalizer (H : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hmem : g • x ∈ B := by
      rw [← mem_stabilizer_iff.mp hg]
      exact Set.smul_mem_smul_set (show x ∈ B from rfl)
    change stabilizer G (g • x) = H at hmem
    rwa [stabilizer_smul_eq_stabilizer_map_conj] at hmem
  have hproperB : stabilizer G B ≠ ⊤ := fun h => hn (top_unique (h ▸ hBN))
  have hi := small_index hc (stabilizer G B) hproperB
  have hb := block_count B (stabilizer_fiber_block H)
  norm_num at hb
  change B.ncard ≤ 2
  nlinarith

/-- Every subgroup of the Witt-design M₁₂ actually isomorphic to A₅ has
inner centralizer of order at most two. -/
public theorem innerCentralizerBound : InnerCentralizerBound := by
  classical
  intro P ⟨e⟩
  let : IsSimpleGroup P := e.isSimpleGroup
  have hc : Nat.card P = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨p, hp⟩ := exists_ne (1 : P)
  have hex : ∃ x : Fin 12, p • x ≠ x := by
    by_contra! h
    apply hp
    apply eq_of_smul_eq_smul (α := Fin 12)
    simpa only [one_smul] using h
  obtain ⟨x, hx⟩ := hex
  have hproper : stabilizer P x ≠ ⊤ := by
    intro h
    exact hx (mem_stabilizer_iff.mp (h ▸ mem_top p))
  have horbit : 5 ≤ (orbit P x).ncard := by
    rw [← index_stabilizer]
    exact small_index hc _ hproper
  let C := centralizer (P : Set M12)
  let : SMulCommClass P C (Fin 12) := ⟨fun p c y => by
    change (p : M12) • ((c : M12) • y) = (c : M12) • ((p : M12) • y)
    rw [← mul_smul, ← mul_smul, mem_centralizer_iff.mp c.property p p.property]⟩
  let B : Set (Fin 12) := {y | stabilizer P y = stabilizer P x}
  let f : C → B := fun c => ⟨c • x, stabilizer_smul_eq_right c x⟩
  have hf : Function.Injective f := by
    intro c d hcd
    have hcdx : c • x = d • x := congrArg Subtype.val hcd
    have hqx : (d⁻¹ * c) • x = x := by rw [mul_smul, hcdx, inv_smul_smul]
    have hcard : Fintype.card (Fin 5) ≤ Fintype.card (orbit P x) := by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_fin, Nat.card_coe_set_eq]
        using horbit
    obtain ⟨a⟩ := Function.Embedding.nonempty_of_card_le hcard
    have hq : ((d⁻¹ * c : C) : M12) = 1 := by
      apply m12_isSharplyFivePretransitive.eq_one_of_fixes_embedding
        (a.trans (Function.Embedding.subtype _))
      intro i
      change (d⁻¹ * c) • (a i).val = (a i).val
      obtain ⟨g, hg⟩ := (a i).property
      rw [← hg, ← smul_comm g (d⁻¹ * c), hqx]
    exact (inv_mul_eq_one.mp (show d⁻¹ * c = 1 from Subtype.ext hq)).symm
  exact (Nat.card_le_card_of_injective f hf).trans (stabilizer_fiber_card hc x hproper)

end Sporadic.Mathieu.M12A5Fixer
