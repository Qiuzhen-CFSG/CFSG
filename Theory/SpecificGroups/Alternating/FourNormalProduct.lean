module
public import Theory.SpecificGroups.Alternating.FourPairAutomorphisms
/-!
# Normal subgroups in a symmetric four-factor product

A normal subgroup of S₄×B whose first projection is even either has a
two-group first image or contains A₄×1. In the latter case a transposition
commutator separates a three-cycle from the other coordinate, and normal
subgroup structure in A₄ finishes the argument. This uses small explicit
permutations, with no subgroup enumeration.

Source application: Aschbacher--Smith, completion of 12.3.1, printed p.811,
identifying the two local residuals through the original S₄×S₃ action.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.Alternating
variable {B : Type*} [Group B]

/-- A normal subgroup of S₄×B with even first image either has a two-group
first image or contains the entire first A₄ factor. -/
theorem normal_four_product_first
    (N : Subgroup (Equiv.Perm (Fin 4) × B)) [N.Normal]
    (hN : N.map (MonoidHom.fst _ _) ≤ alternatingGroup (Fin 4)) :
    IsPGroup 2 (N.map (MonoidHom.fst _ _)) ∨
      (alternatingGroup (Fin 4)).prod (⊥ : Subgroup B) ≤ N := by
  let A := alternatingGroup (Fin 4)
  let F := N.map (MonoidHom.fst _ _)
  let : F.Normal := Normal.map inferInstance _ Prod.fst_surjective
  let I := F.subgroupOf A
  have hc := AlternatingFourPair.normalA4 I
  rcases hc with hc | hc | hc
  · left
    exact (show IsPGroup 2 I by rw [hc]; exact IsPGroup.of_bot).of_equiv
      (subgroupOfEquivOfLe hN)
  · left
    have hp : IsPGroup 2 I := by
      rw [hc]
      change IsPGroup 2 (alternatingGroup.kleinFour (Fin 4))
      rw [← AlternatingFourPair.twoCore_eq_kleinFour]
      exact pCore_isPGroup
    exact hp.of_equiv (subgroupOfEquivOfLe hN)
  · right
    let a : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
    let t : Equiv.Perm (Fin 4) := Equiv.swap 0 1
    have ha : a ∈ A := by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel
    have haF : a ∈ F := show (⟨a,ha⟩ : A) ∈ I from hc.symm ▸ mem_top _
    obtain ⟨x,hx,hxa⟩ := haF
    have hxa' : x.1 = a := hxa
    have ht : t * a * t⁻¹ * a⁻¹ = a := by decide +kernel
    have han : (a, (1 : B)) ∈ N := by
      have hh := N.mul_mem ((inferInstance : N.Normal).conj_mem x hx (t,1)) (N.inv_mem hx)
      convert hh using 1
      apply Prod.ext
      · change a = t * x.1 * t⁻¹ * x.1⁻¹
        rw [hxa',ht]
      · simp
    let j : A →* Equiv.Perm (Fin 4) × B := (MonoidHom.inl _ _).comp A.subtype
    let J := N.comap j
    have haj : (⟨a,ha⟩ : A) ∈ J := han
    have ha1 : (⟨a,ha⟩ : A) ≠ 1 := by
      intro h
      have hh := congrArg (fun z : A => z.val 0) h
      have hh' : (1 : Fin 4) = 0 := hh
      exact (by decide : (1 : Fin 4) ≠ 0) hh'
    have haK : (⟨a,ha⟩ : A) ∉ AlternatingFourPair.K := by
      change (⟨a,ha⟩ : A) ∉ alternatingGroup.kleinFour (Fin 4)
      rw [← SetLike.mem_coe, alternatingGroup.coe_kleinFour_of_card_eq_four (by norm_num)]
      exact not_or.mpr ⟨ha1, (by decide +kernel : a.cycleType ≠ {2,2})⟩
    have hJ : J = ⊤ := by
      rcases AlternatingFourPair.normalA4 J with he | he | he
      · exact False.elim (ha1 (mem_bot.mp (he ▸ haj)))
      · exact False.elim (haK (he ▸ haj))
      · exact he
    rintro ⟨b,c⟩ ⟨hb,hc⟩
    have hc1 : c = 1 := mem_bot.mp hc
    subst c
    exact show (⟨b,hb⟩ : A) ∈ J from hJ.symm ▸ mem_top _
end Theory.SpecificGroups.Alternating
