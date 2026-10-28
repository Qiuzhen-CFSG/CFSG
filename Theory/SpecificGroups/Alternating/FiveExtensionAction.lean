module

public import Theory.Alternating.Aut
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient

/-!
# The five-point action of a group with a normal A₅

A self-centralizing normal A₅ gives a faithful action on five letters by
Aut(A₅) = S₅. An element inducing an outer automorphism has odd image, so
this action is onto. The resulting equivalence extends the prescribed A₅
identification; it therefore retains the Sylow markings used on modules.
For a group with trivial two-core and two-group quotient by A₅, the needed
centralizer vanishing is proved from those structural hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed p.955; the automorphism theorem is GLS3, 5.2.1.
-/

public section
open Subgroup

namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
/-- The actual conjugation isomorphism S₅ ≃ Aut(A₅). -/
noncomputable def symmetricAutEquiv :
    Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))

variable {H : Type*} [Group H] (K : Subgroup H) [K.Normal]

/-- Conjugation on a normal A₅, viewed on its five letters. -/
noncomputable def action (eK : K ≃* alternatingGroup (Fin 5)) : H →* Equiv.Perm (Fin 5) :=
  symmetricAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr eK).toMonoidHom.comp MulAut.conjNormal)

/-- The action extends the specified five-point action of K. -/
theorem action_on_subgroup (eK : K ≃* alternatingGroup (Fin 5)) (k : K) :
    action K eK k = eK k := by
  apply symmetricAutEquiv.injective
  change symmetricAutEquiv (symmetricAutEquiv.symm _) = MulAut.conjNormal (eK k).val
  rw [symmetricAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (eK (k * eK.symm y * k⁻¹)).val = (eK k).val * y.val * (eK k).val⁻¹
  simp

/-- Trivial centralizer makes the permutation action faithful. -/
theorem action_injective (eK : K ≃* alternatingGroup (Fin 5))
    (hC : centralizer (K : Set H) = ⊥) : Function.Injective (action K eK) :=
  symmetricAutEquiv.symm.injective.comp
    ((MulAut.congr eK).injective.comp
      (MulAut.conjNormal_injective_of_centralizer_eq_bot K hC))

/-- An outer actor supplies an odd permutation; together with A₅ this fills S₅. -/
theorem action_surjective (eK : K ≃* alternatingGroup (Fin 5))
    (t : H) (ht : (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K) :
    Function.Surjective (action K eK) := by
  have hout : action K eK t ∉ alternatingGroup (Fin 5) := by
    intro h
    let k : K := eK.symm ⟨action K eK t, h⟩
    apply ht
    refine ⟨k, ?_⟩
    apply (MulAut.congr eK).injective
    apply symmetricAutEquiv.symm.injective
    have ha : action K eK k = action K eK t :=
      (action_on_subgroup K eK k).trans (congrArg Subtype.val (eK.apply_symm_apply _))
    simpa only [action, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conjNormal_val] using ha
  have heven (a : Equiv.Perm (Fin 5)) (ha : a ∈ alternatingGroup (Fin 5)) :
      ∃ x : H, action K eK x = a := by
    obtain ⟨x, hx⟩ := eK.surjective ⟨a, ha⟩
    exact ⟨x, (action_on_subgroup K eK x).trans (congrArg Subtype.val hx)⟩
  intro a
  by_cases ha : a ∈ alternatingGroup (Fin 5)
  · exact heven a ha
  · have hprod : a * (action K eK t)⁻¹ ∈ alternatingGroup (Fin 5) := by
      rw [mul_mem_iff_of_index_two alternatingGroup.index_eq_two, inv_mem_iff]
      exact iff_of_false ha hout
    obtain ⟨x, hx⟩ := heven _ hprod
    exact ⟨x * t, by rw [map_mul, hx, inv_mul_cancel_right]⟩

/-- A self-centralizing normal A₅ and one outer actor identify the whole
group with S₅, compatibly with the given identification of A₅. -/
theorem exists_equiv (eK : K ≃* alternatingGroup (Fin 5))
    (hC : centralizer (K : Set H) = ⊥)
    (t : H) (ht : (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K) :
    ∃ e : H ≃* Equiv.Perm (Fin 5), ∀ k : K, e k = eK k := by
  refine ⟨MulEquiv.ofBijective (action K eK)
    ⟨action_injective K eK hC, action_surjective K eK t ht⟩, ?_⟩
  exact action_on_subgroup K eK

/-- In a group with trivial two-core, the normal A₅ with two-group quotient
is self-centralizing. This discharges the faithfulness input to `exists_equiv`. -/
theorem exists_equiv_of_two_quotient (eK : K ≃* alternatingGroup (Fin 5))
    (hquot : IsPGroup 2 (H ⧸ K)) (hcore : pCore 2 H = ⊥)
    (t : H) (ht : (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K) :
    ∃ e : H ≃* Equiv.Perm (Fin 5), ∀ k : K, e k = eK k := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hn : ¬ IsMulCommutative K := by
    intro h
    have hA : IsMulCommutative (alternatingGroup (Fin 5)) :=
      isMulCommutative_iff.mpr (fun a b => eK.symm.injective (by
        simpa only [map_mul] using (isMulCommutative_iff.mp h) (eK.symm a) (eK.symm b)))
    have := alternatingGroup.isMulCommutative_iff_card_le_three.mp hA
    norm_num at this
  exact exists_equiv K eK
    (Theory.GroupTheory.centralizer_eq_bot_of_simple_two_quotient K hn hquot hcore) t ht

/-- A two-subgroup supplement gives the required two-group quotient, without
assuming that the extension splits or that the two-subgroup is disjoint from K. -/
theorem exists_equiv_of_two_supplement (eK : K ≃* alternatingGroup (Fin 5))
    (T : Subgroup H) (hT : IsPGroup 2 T) (hKT : K ⊔ T = ⊤)
    (hcore : pCore 2 H = ⊥)
    (t : H) (ht : (MulAut.conjNormal t : MulAut K) ∉ MulAut.innerSubgroup K) :
    ∃ e : H ≃* Equiv.Perm (Fin 5), ∀ k : K, e k = eK k := by
  let q := QuotientGroup.mk' K
  have hqK : K.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hqT : T.map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hKT
    rw [Subgroup.map_sup, hqK, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective K)] at h
    exact h
  have hsurj : Function.Surjective (q.comp T.subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype]
    exact hqT
  exact exists_equiv_of_two_quotient K eK
    (hT.of_surjective (q.comp T.subtype) hsurj) hcore t ht

end Theory.SpecificGroups.Alternating.FiveExtensionAction
