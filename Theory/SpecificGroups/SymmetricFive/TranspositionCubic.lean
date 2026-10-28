module
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic.Movement
/-!
# Transposition pushing-up geometry on the binary five-point core

An overlapping cubic moves a vector fixed by a transposition and generates
S₅ with its normalizer. Conjugacy transports the standard pair to any
transposition. The same coordinates then show that its lift in a Thompson
subgroup moves the original omega-center span in the cubic preimage.

This is the native input to C.1.24(a) for an intermediate two-group with
transposition image, as used on Q₂ in 13.2.12, printed p.882.
Source: Aschbacher--Smith C.1.21(4) and C.1.24, printed pp.129--131.
-/

@[expose] public section

open Subgroup Equiv Representation.BinaryOffender BinaryPermutation
namespace Theory.SpecificGroups.SymmetricFive.TranspositionCubic
abbrev Sym := Perm (Fin 5)
def reflection : Sym := swap 0 1
def cubic : Sym := swap 0 1 * swap 1 2

theorem reflection_square : reflection^2=1 := by decide +kernel
theorem cubic_cube : cubic^3=1 := by decide +kernel
theorem cubic_even : cubic ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

theorem normalizer_cubic_generate :
    normalizer (zpowers reflection : Set Sym) ⊔ zpowers cubic = ⊤ := by
  let N := normalizer (zpowers reflection : Set Sym) ⊔ zpowers cubic
  have hr : reflection ∈ N := (show normalizer (zpowers reflection : Set Sym) ≤ N from le_sup_left) ((zpowers reflection).le_normalizer (mem_zpowers reflection))
  have hc : cubic ∈ N := (show zpowers cubic ≤ N from le_sup_right) (mem_zpowers cubic)
  have h12 : swap (1:Fin 5) 2 ∈ N := by
    have he : reflection*cubic=swap (1:Fin 5) 2 := by decide +kernel
    rw [←he]
    exact N.mul_mem hr hc
  have hother : ∀ i : Fin 4, 2 ≤ i.val → swap i.castSucc i.succ ∈ N := by
    intro i hi
    apply (show normalizer (zpowers reflection : Set Sym) ≤ N from le_sup_left)
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    congr 1
    fin_cases i <;> norm_num at hi
    all_goals decide +kernel
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Perm.mclosure_swap_castSucc_succ 4)]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨i,rfl⟩
  fin_cases i
  · exact hr
  · exact h12
  · exact hother 2 (by decide)
  · exact hother 3 (by decide)

private def pairVector : core (Fin 5) :=
  ⟨Pi.single 0 1 + Pi.single 1 1,by simp [mem_core];decide⟩

theorem cubic_moves_reflection_fixed :
    ¬fixedSpace (coreRepresentation (Fin 5)) (zpowers reflection) ≤
      fixedSpace (coreRepresentation (Fin 5)) (zpowers cubic) := by
  intro h
  have hr : pairVector ∈ fixedSpace (coreRepresentation (Fin 5)) (zpowers reflection) := by
    rw [zpowers_eq_closure,mem_fixedSpace_closure_iff]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    decide +kernel
  have hc := (h hr) ⟨cubic,mem_zpowers cubic⟩
  have hn : coreRepresentation (Fin 5) cubic pairVector ≠ pairVector := by decide +kernel
  exact hn hc

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
    (A : Subgroup Sym) (g : Sym) (v : core (Fin 5))
    (hv : v ∈ fixedSpace (coreRepresentation (Fin 5)) A) :
    coreRepresentation (Fin 5) g v ∈ fixedSpace (coreRepresentation (Fin 5))
      (A.map (MulAut.conj g).toMonoidHom) := by
  rintro ⟨_,a,ha,rfl⟩
  change coreRepresentation (Fin 5) (g*a*g⁻¹) (coreRepresentation (Fin 5) g v)=_
  rw [map_mul,map_mul]
  simp only [Module.End.mul_apply,Representation.inv_self_apply]
  exact congrArg (coreRepresentation (Fin 5) g) (hv ⟨a,ha⟩)

private theorem fixed_conj_back
    (A : Subgroup Sym) (g : Sym) (v : core (Fin 5))
    (hv : coreRepresentation (Fin 5) g v ∈ fixedSpace (coreRepresentation (Fin 5))
      (A.map (MulAut.conj g).toMonoidHom)) :
    v ∈ fixedSpace (coreRepresentation (Fin 5)) A := by
  intro a
  have hh := congrArg (coreRepresentation (Fin 5) g⁻¹)
    (hv ⟨g*(a:Sym)*g⁻¹,a,a.property,rfl⟩)
  change coreRepresentation (Fin 5) g⁻¹
    (coreRepresentation (Fin 5) (g*(a:Sym)*g⁻¹) (coreRepresentation (Fin 5) g v))=
      coreRepresentation (Fin 5) g⁻¹ (coreRepresentation (Fin 5) g v) at hh
  change coreRepresentation (Fin 5) (a:Sym) v=v
  simpa only [map_mul,Module.End.mul_apply,Representation.inv_self_apply] using hh

theorem exists_cubic_for_transposition (r : Sym) (hr : r.IsSwap) :
    ∃ c : Sym, orderOf c=3 ∧ c ∈ alternatingGroup (Fin 5) ∧ r*c*r⁻¹=c⁻¹ ∧
      normalizer (zpowers r : Set Sym) ⊔ zpowers c=⊤ ∧
      Nat.card (zpowers c ⊔ zpowers r : Subgroup Sym)=6 ∧
      ¬fixedSpace (coreRepresentation (Fin 5)) (zpowers r) ≤
        fixedSpace (coreRepresentation (Fin 5)) (zpowers c) := by
  obtain ⟨i,j,hij,rfl⟩ := hr
  obtain ⟨g,hg⟩ := isConj_iff.mp (Perm.isConj_swap (w := (0:Fin 5)) (x := 1) (by decide) hij)
  let e := MulAut.conj g
  have he : e reflection = swap i j := hg
  have hem : e.toMonoidHom reflection = swap i j := he
  refine ⟨e cubic,?_,?_,?_,?_,?_,?_⟩
  · exact (e.orderOf_eq cubic).trans cubic_order
  · exact (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem
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
    change coreRepresentation (Fin 5) g v ∈ fixedSpace (coreRepresentation (Fin 5))
      (zpowers (e reflection)) at hh
    rw [he] at hh
    apply fixed_conj_back (zpowers cubic) g v
    rw [MonoidHom.map_zpowers]
    exact h hh

open Stellmacher Representation.BinaryOffender
variable {G : Type*} [Group G]
theorem omega_span_moved (V R A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (q : G →* Sym)
    (e : V ≃* Multiplicative (BinaryPermutation.core (Fin 5)))
    (he : ∀ (g : G) (v : V), (e (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 5) (q g) (e v).toAdd)
    (r c : Sym) (hR : R.map q ≤ zpowers r) (hrA : r ∈ A.map q) (hcG : c ∈ q.range)
    (hc : c^3=1) (hi : r*c*r⁻¹=c⁻¹)
    (hm : ¬fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (zpowers r) ≤
      fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (zpowers c)) :
    ¬ A ≤ centralizer (normalClosure (omegaOneCenterAmbient R : Set G) : Set G) := by
  obtain ⟨v,hv,hcv⟩ := exists_moved_cubic_translate _ r c hc hi hm
  let u : V := e.symm (Multiplicative.ofAdd v)
  have heu : (e u).toAdd=v := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  have huv : v ∈ fixedSpace (BinaryPermutation.coreRepresentation (Fin 5)) (zpowers r) :=
    (mem_fixedSpace_zpowers_iff _ _ _).mpr hv
  have huR : (u:G) ∈ omegaOneCenterAmbient R := by
    apply (mem_omegaOneCenterAmbient_iff R (u:G)).mpr
    refine ⟨hVR u.property,elemPow_eq_one_of_isElementaryAbelian (u:G) u.property,?_⟩
    intro a ha
    have hfix : MulAut.conjNormal a u=u := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [he,heu]
      exact huv ⟨q a,hR (mem_map_of_mem q ha)⟩
    have hh := congrArg (fun z : V => (z:G)) hfix
    change a*(u:G)*a⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  obtain ⟨g,hg⟩ := hcG
  let w : V := MulAut.conjNormal g u
  have hw : (w:G) ∈ normalClosure (omegaOneCenterAmbient R : Set G) :=
    (normalClosure_normal.conj_mem _ (subset_normalClosure huR) g)
  obtain ⟨a,ha,hqa⟩ := hrA
  intro hA
  have hfix : MulAut.conjNormal a w=w := by
    apply Subtype.ext
    change a*(w:G)*a⁻¹=(w:G)
    rw [←hA ha (w:G) hw]
    group
  have hh := he a w
  rw [hfix,hqa] at hh
  have hwcoord : (e w).toAdd=BinaryPermutation.coreRepresentation (Fin 5) c v := by
    rw [show w=MulAut.conjNormal g u from rfl,he,hg,heu]
  rw [hwcoord] at hh
  exact hcv hh.symm
end Theory.SpecificGroups.SymmetricFive.TranspositionCubic
