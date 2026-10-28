module

public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.Alternating.Aut
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Two-group extensions of an alternating-five core quotient

If a two-group S normalizes K and K/O₂(K) is A₅, then KS/O₂(KS) is
A₅ or S₅. The quotient action has kernel exactly O₂(KS), since A₅ is
centerless. Its five-point image contains A₅ and is therefore A₅ or S₅.
No containment of S in K, splitting, or bound on O₂(KS) is assumed.

Source application: Aschbacher--Smith, F.1.12(I) and original 9.3.1,
printed pp.262--264 and 732 of refs/quasithin.pdf. This is the local
extension calculation, not the recognition of a rank-two amalgam.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.Alternating.FiveExtensionAction
variable {G : Type*} [Group G]

private theorem a5_centerless {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) : center H = ⊥ := by
  apply bot_unique
  intro z hz
  apply e.injective
  have he : e z ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz x)
  simpa only [alternatingGroup.center_eq_bot (α := Fin 5) (by simp), mem_bot, map_one] using he

/-- A two-group supplement extends an A₅ core quotient only to A₅ or S₅. -/
theorem core_quotient_of_two_supplement (K S : Subgroup G)
    (hn : S ≤ normalizer (K : Set G)) (hp : IsPGroup 2 S)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    Nonempty (((K ⊔ S : Subgroup G) ⧸ pCore 2 (K ⊔ S : Subgroup G)) ≃*
      alternatingGroup (Fin 5)) ∨
    Nonempty (((K ⊔ S : Subgroup G) ⧸ pCore 2 (K ⊔ S : Subgroup G)) ≃*
      Equiv.Perm (Fin 5)) := by
  let E : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        5 (by decide) (by decide))
  let a : (K ⊔ S : Subgroup G) →* Equiv.Perm (Fin 5) :=
    E.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp (pCoreJoinAction 2 hn))
  have ha : a.ker = pCore 2 (K ⊔ S : Subgroup G) := by
    rw [show a.ker = _ from rfl,
      MonoidHom.ker_comp_of_injective _ _ E.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
      pCoreJoinAction_kernel 2 hn hp (a5_centerless e)]
  have hA : alternatingGroup (Fin 5) ≤ a.range := by
    intro x hx
    obtain ⟨k, hk⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 K))) ⟨x,hx⟩
    change e (QuotientGroup.mk' (pCore 2 K) k) = ⟨x,hx⟩ at hk
    refine ⟨inclusion le_sup_left k, ?_⟩
    change E.symm (MulAut.congr e (pCoreJoinAction 2 hn (inclusion le_sup_left k))) = x
    rw [pCoreJoinAction_on_component, MulAut.congr_conj, hk]
    apply E.injective
    rw [E.apply_symm_apply]
    rfl
  have hi : a.range.index = 1 ∨ a.range.index = 2 := by
    apply (Nat.dvd_prime Nat.prime_two).mp
    have hd := index_dvd_of_le hA
    rwa [alternatingGroup.index_eq_two] at hd
  let d : ((K ⊔ S : Subgroup G) ⧸ pCore 2 (K ⊔ S : Subgroup G)) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq ha.symm).trans
      (QuotientGroup.quotientKerEquivRange a)
  rcases hi with hi | hi
  · exact Or.inr ⟨(d.trans (MulEquiv.subgroupCongr (index_eq_one.mp hi))).trans topEquiv⟩
  · have heq : alternatingGroup (Fin 5) = a.range := by
      apply eq_of_le_of_card_ge hA
      have hm := a.range.index_mul_card
      have hS5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
        simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
      rw [hS5, hi] at hm
      have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
        rw [nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      change Nat.card a.range ≤ Nat.card (alternatingGroup (Fin 5))
      rw [hA5]
      omega
    exact Or.inl ⟨d.trans (MulEquiv.subgroupCongr heq.symm)⟩


end Theory.SpecificGroups.Alternating.FiveExtensionAction
