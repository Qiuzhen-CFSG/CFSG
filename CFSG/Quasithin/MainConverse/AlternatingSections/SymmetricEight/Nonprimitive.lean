module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.Basic
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Data.Fintype.Option

/-!
# Nonprimitive simple quotients in degrees seven and eight

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
condition K on printed pp.4 and 482. This is the conditional nonprimitive
step in the degree-eight section calculation: the constructed-section
property of every smaller symmetric group is an explicit premise.

An intransitive faithful action restricts injectively to the product of
its actions on an orbit and its complement. For a transitive imprimitive
action, the kernel of the action on block translates embeds in the product
of the permutation groups on the individual blocks; the quotient embeds
in the permutation group on the block set. All these degrees are smaller.
Finite-product closure follows by splitting off one coordinate, and the
normal-section alternative supplies extension closure. The final quotient
is transported to an arbitrary universe through its actual isomorphism.

The orbit and restriction arguments adapt the existing degree-nine
calculation in `AlternatingSections/NineReduction/Nonprimitive.lean`.
-/

namespace CFSG.Quasithin.MainConverse.SymmetricEight
open CFSG.KnownSimple
open scoped Pointwise

/-- Jointly injective homomorphisms give the product reduction: the kernel
of the first embeds in the second target, and the quotient embeds in the first. -/
private theorem isKGroup_of_two_homs {H A B : Type*} [Group H] [Group A] [Group B]
    (hA : IsKGroup IsConstructedCarrier A) (hB : IsKGroup IsConstructedCarrier B)
    (a : H →* A) (b : H →* B)
    (hi : ∀ x y, a x = a y → b x = b y → x = y) :
    IsKGroup IsConstructedCarrier H := by
  refine IsKGroup.of_normal_quotient (K := IsConstructedCarrier) a.ker ?_ ?_
  · apply isKGroup_constructed_of_injective hB (b.comp a.ker.subtype)
    intro x y hxy
    apply Subtype.ext
    exact hi x y (x.property.trans y.property.symm) hxy
  · let q : H ⧸ a.ker →* A :=
      a.range.subtype.comp (QuotientGroup.quotientKerEquivRange a).toMonoidHom
    exact isKGroup_constructed_of_injective hA q
      (a.range.subtype_injective.comp (QuotientGroup.quotientKerEquivRange a).injective)

universe u v
/-- Finite products of groups with constructed simple sections have the same property. -/
private theorem isKGroup_pi {ι : Type u} [Finite ι]
    (A : ι → Type v) [∀ i, Group (A i)]
    (hA : ∀ i, IsKGroup IsConstructedCarrier (A i)) :
    IsKGroup IsConstructedCarrier (∀ i, A i) := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    let f : (∀ i, A i) →* (∀ j, A (e j)) :=
      { toFun := fun x j => x (e j), map_one' := rfl, map_mul' := fun _ _ => rfl }
    apply isKGroup_constructed_of_injective (ih (fun j => A (e j)) (fun j => hA (e j))) f
    intro x y hxy
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun hxy j
  | h_empty => exact solvable_isKGroup_constructed _
  | h_option ih =>
    let a : (∀ i, A i) →* A none :=
      { toFun := fun x => x none, map_one' := rfl, map_mul' := fun _ _ => rfl }
    let b : (∀ i, A i) →* (∀ j, A (some j)) :=
      { toFun := fun x j => x (some j), map_one' := rfl, map_mul' := fun _ _ => rfl }
    apply isKGroup_of_two_homs (hA none) (ih (fun j => A (some j)) (fun j => hA (some j))) a b
    intro x y ha hb
    funext i
    cases i with
    | none => exact ha
    | some j => exact congrFun hb j

private theorem isKGroup_perm_of_card_lt {n : ℕ}
    (hsmall : ∀ m, m < n → IsKGroup IsConstructedCarrier (Equiv.Perm (Fin m)))
    {X : Type*} [Finite X] (hX : Nat.card X < n) :
    IsKGroup IsConstructedCarrier (Equiv.Perm X) := by
  let e := Equiv.permCongrHom (Finite.equivFin X)
  exact isKGroup_constructed_of_injective (hsmall _ hX) e.toMonoidHom e.injective

/-- The actual restriction of a permutation representation to an invariant subset. -/
private def restrictionHom {H X : Type*} [Group H] (i : H →* Equiv.Perm X)
    (t : Set X) (ht : ∀ g x, i g x ∈ t ↔ x ∈ t) : H →* Equiv.Perm t where
  toFun g := (i g).subtypePerm (ht g)
  map_one' := by apply Equiv.ext; intro x; apply Subtype.ext; exact congrArg (fun p => p x) i.map_one
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun p => p x) (i.map_mul g h)

private theorem isKGroup_of_invariant_subset {n : ℕ}
    (hsmall : ∀ m, m < n → IsKGroup IsConstructedCarrier (Equiv.Perm (Fin m)))
    {H : Type*} [Group H] (i : H →* Equiv.Perm (Fin n)) (hi : Function.Injective i)
    (t : Set (Fin n)) (ht : t.Nonempty) (htc : tᶜ.Nonempty)
    (hinv : ∀ g x, i g x ∈ t ↔ x ∈ t) :
    IsKGroup IsConstructedCarrier H := by
  have hcard : ∀ a : Set (Fin n), aᶜ.Nonempty → Nat.card a < n := by
    intro a ha
    have hne : a ≠ Set.univ := Set.nonempty_compl.mp ha
    change a.ncard < n
    simpa only [Nat.card_fin] using Set.ncard_lt_card hne
  let a := restrictionHom i t hinv
  let b := restrictionHom i tᶜ (fun g x => not_congr (hinv g x))
  apply isKGroup_of_two_homs (isKGroup_perm_of_card_lt hsmall (hcard t htc))
    (isKGroup_perm_of_card_lt hsmall (hcard tᶜ (by simpa only [compl_compl] using ht))) a b
  intro g h ha hb
  apply hi
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ t
  · exact congrArg (fun p : Equiv.Perm t => (p ⟨x, hx⟩).val) ha
  · exact congrArg (fun p : Equiv.Perm ↥(tᶜ) => (p ⟨x, hx⟩).val) hb

private theorem isKGroup_of_intransitive {n : ℕ}
    (hsmall : ∀ m, m < n → IsKGroup IsConstructedCarrier (Equiv.Perm (Fin m)))
    {H : Type*} [Group H] [MulAction H (Fin n)] [FaithfulSMul H (Fin n)]
    (ht : ¬ MulAction.IsPretransitive H (Fin n)) :
    IsKGroup IsConstructedCarrier H := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : Fin n, y ∉ MulAction.orbit H x := by
    by_contra! h
    exact ht ⟨fun x y => MulAction.mem_orbit_iff.mp (h x y)⟩
  apply isKGroup_of_invariant_subset hsmall (MulAction.toPermHom H (Fin n))
    MulAction.toPerm_injective (MulAction.orbit H x) ⟨x, MulAction.mem_orbit_self x⟩
    ⟨y, hxy⟩
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

private theorem isKGroup_of_imprimitive {n : ℕ} (hn : 0 < n)
    (hsmall : ∀ m, m < n → IsKGroup IsConstructedCarrier (Equiv.Perm (Fin m)))
    {H : Type*} [Group H] [MulAction H (Fin n)] [FaithfulSMul H (Fin n)]
    [MulAction.IsPretransitive H (Fin n)]
    (hp : ¬ MulAction.IsPreprimitive H (Fin n)) :
    IsKGroup IsConstructedCarrier H := by
  classical
  obtain ⟨B, hB, hBs, hBu⟩ : ∃ B : Set (Fin n),
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
  have hmul := hB.ncard_block_mul_ncard_orbit_eq hBne
  simp only [Nat.card_fin] at hmul
  have hdeg : Nat.card (MulAction.orbit H B) < n := by
    change (MulAction.orbit H B).ncard < n
    nlinarith
  let a := MulAction.toPermHom H (MulAction.orbit H B)
  refine IsKGroup.of_normal_quotient (K := IsConstructedCarrier) a.ker ?_ ?_
  · let i : a.ker →* Equiv.Perm (Fin n) :=
      (MulAction.toPermHom H (Fin n)).comp a.ker.subtype
    have hfix (k : a.ker) (C : MulAction.orbit H B) : (k : H) • C.val = C.val :=
      congrArg (fun p : Equiv.Perm (MulAction.orbit H B) => (p C).val) k.property
    have hinv (C : MulAction.orbit H B) (k : a.ker) (x : Fin n) :
        i k x ∈ C.val ↔ x ∈ C.val := by
      change (k : H) • x ∈ C.val ↔ x ∈ C.val
      calc
        (k : H) • x ∈ C.val ↔ (k : H) • x ∈ (k : H) • C.val := by rw [hfix]
        _ ↔ x ∈ C.val := Set.smul_mem_smul_set_iff
    let r (C : MulAction.orbit H B) : a.ker →* Equiv.Perm C.val :=
      restrictionHom i C.val (hinv C)
    let p : a.ker →* (∀ C : MulAction.orbit H B, Equiv.Perm C.val) :=
      { toFun := fun k C => r C k
        map_one' := by funext C; exact (r C).map_one
        map_mul' := fun k l => by funext C; exact (r C).map_mul k l }
    have hC (C : MulAction.orbit H B) : Nat.card C.val < n := by
      change C.val.ncard < n
      have hCu : C.val ≠ Set.univ := by
        obtain ⟨g, hg⟩ := C.property
        intro heq
        apply hBu
        have hgb : g • B = Set.univ := hg.trans heq
        have := congrArg (fun t : Set (Fin n) => g⁻¹ • t) hgb
        simpa only [inv_smul_smul, Set.smul_set_univ] using this
      simpa only [Nat.card_fin] using Set.ncard_lt_card hCu
    apply isKGroup_constructed_of_injective
      (isKGroup_pi (fun C : MulAction.orbit H B => Equiv.Perm C.val)
        (fun C => isKGroup_perm_of_card_lt hsmall (hC C))) p
    intro k l hkl
    apply Subtype.ext
    apply MulAction.toPerm_injective (β := Fin n)
    apply Equiv.ext
    intro x
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H b x
    let C : MulAction.orbit H B := ⟨g • B, MulAction.mem_orbit B g⟩
    have hx : x ∈ C.val := ⟨b, hb, hg⟩
    exact congrArg (fun q : Equiv.Perm C.val => (q ⟨x, hx⟩).val) (congrFun hkl C)
  · let q : H ⧸ a.ker →* Equiv.Perm (MulAction.orbit H B) :=
      a.range.subtype.comp (QuotientGroup.quotientKerEquivRange a).toMonoidHom
    exact isKGroup_constructed_of_injective (isKGroup_perm_of_card_lt hsmall hdeg) q
      (a.range.subtype_injective.comp (QuotientGroup.quotientKerEquivRange a).injective)

end CFSG.Quasithin.MainConverse.SymmetricEight

namespace CFSG.Quasithin.MainConverse
open CFSG.KnownSimple
open SymmetricEight

/-- Assuming the smaller-degree K-group statements, every simple quotient
of a nonprimitive subgroup of S₇ or S₈ is a constructed carrier. The action
is the standard subgroup action, and the target may inhabit any universe. -/
public theorem nonprimitive_simple_quotient_constructed {n : ℕ} (hn : n = 7 ∨ n = 8)
    (hsmall : ∀ m, m < n → IsKGroup IsConstructedCarrier (Equiv.Perm (Fin m)))
    (U : Subgroup (Equiv.Perm (Fin n)))
    (hp : ¬ MulAction.IsPreprimitive U (Fin n))
    {S : Type*} [Group S] [IsSimpleGroup S]
    (f : U →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  have hU : IsKGroup IsConstructedCarrier U := by
    by_cases ht : MulAction.IsPretransitive U (Fin n)
    · let := ht
      exact isKGroup_of_imprimitive (by omega) hsmall hp
    · exact isKGroup_of_intransitive hsmall ht
  let e : (⊤ : Subgroup U) ≃* U := Subgroup.topEquiv
  exact constructed_section_of_isKGroup hU ⊤
    (f.comp e.toMonoidHom) (hf.comp e.surjective)

end CFSG.Quasithin.MainConverse
