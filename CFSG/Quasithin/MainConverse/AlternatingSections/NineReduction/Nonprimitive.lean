module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Nonprimitive degree-nine sections

This is the nonprimitive part of the proper-K calculation for A₉ in
Aschbacher–Smith, Theorem 0.1.2(3), condition K, printed pp.4 and 482.
The degree-eight section statement is an explicit premise with a target
universe independent of the permutation carriers.

For an invariant nonempty proper set, restrict to it and its complement.
The kernel of one restriction embeds in the other permutation group, and
the quotient embeds in the first. The normal-subgroup alternative transfers
an arbitrary simple section to one of these two groups. Intransitivity
supplies the invariant set. In the imprimitive case, first take the kernel
of the action on the translates of a nontrivial block. That kernel preserves
the block, while the block action has degree below nine. All maps are actual
homomorphisms, and all quotients use normal subgroups of their own numerator.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction

open CFSG.KnownSimple
open scoped Pointwise

universe u v w

private theorem section_of_injective {A B S : Type*} [Group A] [Group B]
    [Group S] [IsSimpleGroup S]
    (hB : ∀ (U : Subgroup B) (f : U →* S), Function.Surjective f → IsConstructedCarrier S)
    (i : A →* B) (hi : Function.Injective i)
    (U : Subgroup A) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  let e := Subgroup.equivMapOfInjective U i hi
  exact hB (U.map i) (f.comp e.symm.toMonoidHom) (hf.comp e.symm.surjective)

private theorem section_of_two_homs {H A B S : Type*} [Group H] [Group A] [Group B]
    [Group S] [IsSimpleGroup S]
    (hA : ∀ (U : Subgroup A) (f : U →* S), Function.Surjective f → IsConstructedCarrier S)
    (hB : ∀ (U : Subgroup B) (f : U →* S), Function.Surjective f → IsConstructedCarrier S)
    (a : H →* A) (b : H →* B)
    (hi : ∀ x y, a x = a y → b x = b y → x = y)
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  rcases Subgroup.simple_section_normal_or_quotient a.ker U f hf with
    ⟨W, g, hg⟩ | ⟨W, g, hg⟩
  · apply section_of_injective hB (b.comp a.ker.subtype) ?_ W g hg
    intro x y hxy
    apply Subtype.ext
    exact hi x y (x.property.trans y.property.symm) hxy
  · let q : H ⧸ a.ker →* A :=
      a.range.subtype.comp (QuotientGroup.quotientKerEquivRange a).toMonoidHom
    exact section_of_injective hA q
      (a.range.subtype_injective.comp (QuotientGroup.quotientKerEquivRange a).injective) W g hg

/-- A faithful action of degree at most eight transfers the explicit degree-eight premise. -/
public theorem simple_section_of_degree_le_eight
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    {X : Type v} [Finite X] (hX : Nat.card X ≤ 8)
    {H : Type w} [Group H] (i : H →* Equiv.Perm X) (hi : Function.Injective i)
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  classical
  let := Fintype.ofFinite X
  obtain ⟨j⟩ : Nonempty (X ↪ Fin 8) := Function.Embedding.nonempty_of_card_le
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hX)
  exact section_of_injective (h8 S) ((Equiv.Perm.viaEmbeddingHom j).comp i)
    ((Equiv.Perm.viaEmbeddingHom_injective j).comp hi) U f hf

private def restrictionHom {H X : Type*} [Group H] (i : H →* Equiv.Perm X)
    (t : Set X) (ht : ∀ g x, i g x ∈ t ↔ x ∈ t) : H →* Equiv.Perm t where
  toFun g := (i g).subtypePerm (ht g)
  map_one' := by apply Equiv.ext; intro x; apply Subtype.ext; exact congrArg (fun p => p x) i.map_one
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun p => p x) (i.map_mul g h)

/-- Restriction to an invariant set and its complement gives two smaller permutation actions. -/
public theorem simple_section_of_invariant_subset
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    {H : Type v} [Group H] (i : H →* Equiv.Perm (Fin 9)) (hi : Function.Injective i)
    (t : Set (Fin 9)) (ht : t.Nonempty) (htc : tᶜ.Nonempty)
    (hinv : ∀ g x, i g x ∈ t ↔ x ∈ t)
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  have hcard : ∀ a : Set (Fin 9), aᶜ.Nonempty → Nat.card a ≤ 8 := by
    intro a ha
    have hne : a ≠ Set.univ := by
      intro heq
      simp only [heq, Set.compl_univ, Set.not_nonempty_empty] at ha
    have hlt := Set.ncard_lt_card hne
    have heq : Nat.card a = a.ncard := rfl
    rw [← heq] at hlt
    simp only [Nat.card_fin] at hlt
    omega
  let a := restrictionHom i t hinv
  let b := restrictionHom i tᶜ (fun g x => not_congr (hinv g x))
  apply section_of_two_homs
    (fun V g hg => simple_section_of_degree_le_eight h8 (hcard t htc)
      (MonoidHom.id _) Function.injective_id V g hg)
    (fun V g hg => simple_section_of_degree_le_eight h8
      (hcard tᶜ (by simpa only [compl_compl] using ht))
      (MonoidHom.id _) Function.injective_id V g hg) a b ?_ U f hf
  intro g h ha hb
  apply hi
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ t
  · exact congrArg (fun p : Equiv.Perm t => (p ⟨x, hx⟩).val) ha
  · exact congrArg (fun p : Equiv.Perm ↥(tᶜ) => (p ⟨x, hx⟩).val) hb

/-- An intransitive degree-nine action has all simple sections in the constructed catalogue. -/
public theorem simple_section_of_intransitive
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    {H : Type v} [Group H] [MulAction H (Fin 9)] [FaithfulSMul H (Fin 9)]
    (ht : ¬ MulAction.IsPretransitive H (Fin 9))
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin 9, y ∉ MulAction.orbit H x := by
    by_contra! h
    exact ht ⟨fun x y => MulAction.mem_orbit_iff.mp (h x y)⟩
  apply simple_section_of_invariant_subset h8 (MulAction.toPermHom H (Fin 9))
    MulAction.toPerm_injective (MulAction.orbit H x) ⟨x, MulAction.mem_orbit_self x⟩
    ⟨y, hxy⟩ ?_ U f hf
  intro g z
  change g • z ∈ MulAction.orbit H x ↔ z ∈ MulAction.orbit H x
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨g⁻¹ * k, ?_⟩
    change (g⁻¹ * k) • x = z
    change k • x = g • z at hk
    rw [mul_smul, hk, inv_smul_smul]
  · rintro ⟨k, rfl⟩
    exact ⟨g * k, mul_smul _ _ _⟩

/-- The block-action kernel and image reduce an imprimitive degree-nine action to smaller degrees. -/
public theorem simple_section_of_imprimitive
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    {H : Type v} [Group H] [MulAction H (Fin 9)] [FaithfulSMul H (Fin 9)]
    [MulAction.IsPretransitive H (Fin 9)]
    (hp : ¬ MulAction.IsPreprimitive H (Fin 9))
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  obtain ⟨B, hB, hBs, hBu⟩ : ∃ B : Set (Fin 9),
      MulAction.IsBlock H B ∧ ¬ B.Subsingleton ∧ B ≠ Set.univ := by
    by_contra! h
    apply hp
    refine { isTrivialBlock_of_isBlock := ?_ }
    intro B hB
    by_cases hBs : B.Subsingleton
    · exact Or.inl hBs
    · exact Or.inr (h B hB (by simpa using hBs))
  have hBtwo : 2 ≤ B.ncard := by
    have : ¬ B.ncard ≤ 1 := by simpa only [Set.ncard_le_one_iff_subsingleton] using hBs
    omega
  have hBne : B.Nonempty := (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  have hBc : Bᶜ.Nonempty := Set.nonempty_compl.mpr hBu
  have hmul := hB.ncard_block_mul_ncard_orbit_eq hBne
  simp only [Nat.card_fin] at hmul
  have hdeg : Nat.card (MulAction.orbit H B) ≤ 8 := by
    change (MulAction.orbit H B).ncard ≤ 8
    nlinarith
  let a := MulAction.toPermHom H (MulAction.orbit H B)
  rcases Subgroup.simple_section_normal_or_quotient a.ker U f hf with
    ⟨W, g, hg⟩ | ⟨W, g, hg⟩
  · let i : a.ker →* Equiv.Perm (Fin 9) := (MulAction.toPermHom H (Fin 9)).comp a.ker.subtype
    apply simple_section_of_invariant_subset h8 i
      (MulAction.toPerm_injective.comp a.ker.subtype_injective) B hBne hBc ?_ W g hg
    intro k x
    have hfix : (k : H) • B = B :=
      congrArg (fun p : Equiv.Perm (MulAction.orbit H B) =>
        (p ⟨B, MulAction.mem_orbit_self B⟩).val) k.property
    change (k : H) • x ∈ B ↔ x ∈ B
    calc
      (k : H) • x ∈ B ↔ (k : H) • x ∈ (k : H) • B := by rw [hfix]
      _ ↔ x ∈ B := Set.smul_mem_smul_set_iff
  · let q : H ⧸ a.ker →* Equiv.Perm (MulAction.orbit H B) :=
      a.range.subtype.comp (QuotientGroup.quotientKerEquivRange a).toMonoidHom
    exact simple_section_of_degree_le_eight h8 hdeg q
      (a.range.subtype_injective.comp (QuotientGroup.quotientKerEquivRange a).injective) W g hg

/-- All nonprimitive degree-nine actions are covered by the degree-eight premise. -/
public theorem simple_section_of_not_preprimitive
    (h8 : ∀ (S : Type u) [Group S] [IsSimpleGroup S]
      (U : Subgroup (Equiv.Perm (Fin 8))) (f : U →* S),
      Function.Surjective f → IsConstructedCarrier S)
    {H : Type v} [Group H] [MulAction H (Fin 9)] [FaithfulSMul H (Fin 9)]
    (hp : ¬ MulAction.IsPreprimitive H (Fin 9))
    {S : Type u} [Group S] [IsSimpleGroup S]
    (U : Subgroup H) (f : U →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  by_cases ht : MulAction.IsPretransitive H (Fin 9)
  · let := ht
    exact simple_section_of_imprimitive h8 hp U f hf
  · exact simple_section_of_intransitive h8 ht U f hf

end CFSG.Quasithin.MainConverse.NineReduction
