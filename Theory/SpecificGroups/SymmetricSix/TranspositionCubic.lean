module
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
/-!
# A transposition and an overlapping cubic in S₆

The standard transposition (01) and cubic (01)(12) generate a subgroup of
order six. The cubic moves a vector fixed by the transposition in the
actual binary deleted permutation module. Its join with the transposition
normalizer is S₆, since it supplies the missing adjacent transposition.
Conjugacy transports these statements to every original transposition.
Only the short six-letter word identities are checked by kernel reduction.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131. These are the
native action and generation inputs to the original cubic local subgroup.
-/

@[expose] public section

open Subgroup Equiv Representation.BinaryOffender BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.TranspositionCubic
abbrev Sym := Perm (Fin 6)
def reflection : Sym := swap 0 1
def cubic : Sym := swap 0 1 * swap 1 2

theorem reflection_square : reflection^2=1 := by decide +kernel
theorem cubic_cube : cubic^3=1 := by decide +kernel
theorem cubic_even : cubic ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

theorem normalizer_cubic_generate :
    normalizer (zpowers reflection : Set Sym) ⊔ zpowers cubic = ⊤ := by
  let N := normalizer (zpowers reflection : Set Sym) ⊔ zpowers cubic
  have hr : reflection ∈ N := (show normalizer (zpowers reflection : Set Sym) ≤ N from le_sup_left) ((zpowers reflection).le_normalizer (mem_zpowers reflection))
  have hc : cubic ∈ N := (show zpowers cubic ≤ N from le_sup_right) (mem_zpowers cubic)
  have h12 : swap (1:Fin 6) 2 ∈ N := by
    have he : reflection*cubic=swap (1:Fin 6) 2 := by decide +kernel
    rw [←he]
    exact N.mul_mem hr hc
  have hother : ∀ i : Fin 5, 2 ≤ i.val → swap i.castSucc i.succ ∈ N := by
    intro i hi
    apply (show normalizer (zpowers reflection : Set Sym) ≤ N from le_sup_left)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    fin_cases i <;> norm_num at hi
    all_goals decide +kernel
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 5)]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i,rfl⟩
  fin_cases i
  · exact hr
  · exact h12
  · exact hother 2 (by decide)
  · exact hother 3 (by decide)
  · exact hother 4 (by decide)

private def pairVector : core (Fin 6) :=
  ⟨Pi.single 0 1 + Pi.single 1 1,by simp [mem_core];decide⟩

private def pairPoint : natural (Fin 6) :=
  ⟨(constants (Fin 6)).mkQ pairVector.val,⟨pairVector.val,pairVector.property,rfl⟩⟩

theorem cubic_moves_reflection_fixed :
    ¬fixedSpace (naturalRepresentation (Fin 6)) (zpowers reflection) ≤
      fixedSpace (naturalRepresentation (Fin 6)) (zpowers cubic) := by
  intro h
  have hr : pairPoint ∈ fixedSpace (naturalRepresentation (Fin 6)) (zpowers reflection) := by
    rw [zpowers_eq_closure,mem_fixedSpace_closure_iff]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    apply Subtype.ext
    change deletedRepresentation (Fin 6) (swap 0 1) ((constants (Fin 6)).mkQ pairVector.val)=(constants (Fin 6)).mkQ pairVector.val
    rw [deleted_swap_fixed_iff (0:Fin 6) 1 2 (by decide) (by decide)]
    decide
  have hc := (mem_natural_fixedSpace_iff (zpowers cubic) pairVector).mp (h hr) cubic (mem_zpowers cubic)
  obtain ⟨c,hc⟩ := hc
  have h3 := hc 3
  have h0 := hc 0
  change (0 : ZMod 2) = c at h3
  change (0 : ZMod 2)-1 = c at h0
  norm_num at h0
  exact zero_ne_one (h3.trans h0.symm)

theorem cubic_order : orderOf cubic = 3 := orderOf_eq_prime cubic_cube (by decide +kernel)
theorem reflection_order : orderOf reflection = 2 := orderOf_eq_prime reflection_square (by decide +kernel)
theorem reflection_inverts_cubic : reflection*cubic*reflection⁻¹=cubic⁻¹ := by decide +kernel
theorem reflection_normalizes_cubic : zpowers reflection ≤ normalizer (zpowers cubic : Set Sym) := by
  apply zpowers_le.mpr
  rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
  change zpowers (reflection*cubic*reflection⁻¹)=zpowers cubic
  rw [reflection_inverts_cubic,zpowers_inv]
theorem local_card : Nat.card (zpowers cubic ⊔ zpowers reflection : Subgroup Sym) = 6 := by
  have hd : Disjoint (zpowers cubic) (zpowers reflection) := disjoint_of_coprime_natCard (by
    rw [Nat.card_zpowers,Nat.card_zpowers,cubic_order,reflection_order];decide)
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (zpowers cubic) (zpowers reflection) reflection_normalizes_cubic
  rw [Nat.card_zpowers,Nat.card_zpowers,cubic_order,reflection_order,
    hd.eq_bot] at hh
  simpa using hh.symm

private theorem fixed_conj_forward
    (A : Subgroup Sym) (g : Sym) (v : natural (Fin 6))
    (hv : v ∈ fixedSpace (naturalRepresentation (Fin 6)) A) :
    naturalRepresentation (Fin 6) g v ∈ fixedSpace (naturalRepresentation (Fin 6))
      (A.map (MulAut.conj g).toMonoidHom) := by
  rintro ⟨_,a,ha,rfl⟩
  change naturalRepresentation (Fin 6) (g*a*g⁻¹) (naturalRepresentation (Fin 6) g v)=_
  rw [map_mul,map_mul]
  simp only [Module.End.mul_apply,Representation.inv_self_apply]
  exact congrArg (naturalRepresentation (Fin 6) g) (hv ⟨a,ha⟩)

private theorem fixed_conj_back
    (A : Subgroup Sym) (g : Sym) (v : natural (Fin 6))
    (hv : naturalRepresentation (Fin 6) g v ∈ fixedSpace (naturalRepresentation (Fin 6))
      (A.map (MulAut.conj g).toMonoidHom)) :
    v ∈ fixedSpace (naturalRepresentation (Fin 6)) A := by
  intro a
  have hh := congrArg (naturalRepresentation (Fin 6) g⁻¹)
    (hv ⟨g*(a:Sym)*g⁻¹,a,a.property,rfl⟩)
  change naturalRepresentation (Fin 6) g⁻¹
    (naturalRepresentation (Fin 6) (g*(a:Sym)*g⁻¹) (naturalRepresentation (Fin 6) g v))=
      naturalRepresentation (Fin 6) g⁻¹ (naturalRepresentation (Fin 6) g v) at hh
  change naturalRepresentation (Fin 6) (a:Sym) v=v
  simpa only [map_mul,Module.End.mul_apply,Representation.inv_self_apply] using hh

theorem exists_cubic_for_transposition (r : Sym) (hr : r.IsSwap) :
    ∃ c : Sym, orderOf c=3 ∧ c ∈ alternatingGroup (Fin 6) ∧ r*c*r⁻¹=c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c=⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym)=6 ∧
      ¬fixedSpace (naturalRepresentation (Fin 6)) (zpowers r) ≤
        fixedSpace (naturalRepresentation (Fin 6)) (zpowers c) := by
  obtain ⟨i,j,hij,rfl⟩ := hr
  obtain ⟨g,hg⟩ := isConj_iff.mp (Perm.isConj_swap (w := (0:Fin 6)) (x := 1) (by decide) hij)
  let e := MulAut.conj g
  have he : e reflection = swap i j := hg
  have hem : e.toMonoidHom reflection = swap i j := he
  refine ⟨e cubic,?_,?_,?_,?_,?_,?_⟩
  · exact (e.orderOf_eq cubic).trans cubic_order
  · exact (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem
      cubic cubic_even g
  · rw [←he,←map_mul,←map_inv,←map_mul,reflection_inverts_cubic,map_inv]
  · have hh := congrArg (Subgroup.map e.toMonoidHom) normalizer_cubic_generate
    rwa [Subgroup.map_sup,map_equiv_normalizer_eq,MonoidHom.map_zpowers,MonoidHom.map_zpowers,
      map_top_of_surjective _ e.surjective,hem] at hh
  · have hh := card_map_of_injective (K := zpowers cubic ⊔ zpowers reflection) (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,hem] at hh
    exact hh.trans local_card
  · intro h
    apply cubic_moves_reflection_fixed
    intro v hv
    have hh := fixed_conj_forward (zpowers reflection) g v hv
    rw [MonoidHom.map_zpowers] at hh
    change naturalRepresentation (Fin 6) g v ∈ fixedSpace (naturalRepresentation (Fin 6))
      (zpowers (e reflection)) at hh
    rw [he] at hh
    apply fixed_conj_back (zpowers cubic) g v
    rw [MonoidHom.map_zpowers]
    exact h hh
end Theory.SpecificGroups.SymmetricSix.TranspositionCubic
