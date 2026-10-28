module

public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Alternating.Aut

/-!
# The normalizer of the natural binary A₅ action

Every automorphism of the additive group of the natural binary module which
normalizes the actual A₅ image is induced by a permutation of its five coordinates.

We first work in the even-weight core of the five-dimensional permutation module.
The two cycles (1 2 3) and (2 3 4) fix precisely zero and the vector supported away
from 0. Its five A₅ translates generate the core. An invertible additive map
commuting with A₅ therefore fixes all five vectors and is the identity. These small
coordinate facts are checked by kernel reduction over the binary coordinates.
Transport through `coreEquivNatural` proves the same centralizer statement for the
literal natural module. Finally, Aut(A₅) = S₅ reduces any normalizing automorphism
to this centralizer calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §B.3
(the natural module), with applications in C.1.13(c), printed pp.124–125,
and C.5.4(3), printed p.155. This module proves the concrete representation
normalizer needed in those applications, independently of their block hypotheses.
-/

namespace BinaryPermutation

private def weightFour (i : Fin 5) : Full (Fin 5) := fun k => if k = i then 0 else 1

private theorem weightFour_mem : ∀ i, weightFour i ∈ core (Fin 5) := by
  change ∀ i, ∑ k, weightFour i k = 0
  decide +kernel

private def corePoint (i : Fin 5) : core (Fin 5) := ⟨weightFour i, weightFour_mem i⟩

private def cycleA : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 1 3
private def cycleB : Equiv.Perm (Fin 5) := Equiv.swap 2 3 * Equiv.swap 2 4

private theorem cycles_even :
    cycleA ∈ alternatingGroup (Fin 5) ∧ cycleB ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem cycles_fix :
    coreRepresentation (Fin 5) cycleA (corePoint 0) = corePoint 0 ∧
    coreRepresentation (Fin 5) cycleB (corePoint 0) = corePoint 0 := by
  constructor <;> apply Subtype.ext <;> decide +kernel

private theorem cycles_fixed (v : core (Fin 5))
    (ha : coreRepresentation (Fin 5) cycleA v = v)
    (hb : coreRepresentation (Fin 5) cycleB v = v) : v = 0 ∨ v = corePoint 0 := by
  have h : ∀ v : Full (Fin 5), (∑ k, v k) = 0 →
      (∀ k, v (cycleA.symm k) = v k) → (∀ k, v (cycleB.symm k) = v k) →
      v = 0 ∨ v = weightFour 0 := by decide +kernel
  rcases h v v.property (fun k => congrArg (fun u : core (Fin 5) => u.val k) ha)
    (fun k => congrArg (fun u : core (Fin 5) => u.val k) hb) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

private def pointMover (i : Fin 5) : Equiv.Perm (Fin 5) :=
  ![1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2, Equiv.swap 0 4 * Equiv.swap 1 2] i

private theorem pointMover_even : ∀ i, pointMover i ∈ alternatingGroup (Fin 5) := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem pointMover_apply (i : Fin 5) :
    coreRepresentation (Fin 5) (pointMover i) (corePoint 0) = corePoint i := by
  apply Subtype.ext
  exact (show ∀ i, representation (Fin 5) (pointMover i) (weightFour 0) =
    weightFour i by decide +kernel) i

private theorem corePoint_generate (v : core (Fin 5)) :
    v = 0 ∨ (∃ i, v = corePoint i) ∨ (∃ i j, v = corePoint i + corePoint j) := by
  have h : ∀ v : Full (Fin 5), (∑ k, v k) = 0 →
      v = 0 ∨ (∃ i, v = weightFour i) ∨ (∃ i j, v = weightFour i + weightFour j) := by
    decide +kernel
  rcases h v v.property with h | ⟨i, h⟩ | ⟨i, j, h⟩
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl ⟨i, Subtype.ext h⟩)
  · exact Or.inr (Or.inr ⟨i, j, Subtype.ext h⟩)

private theorem core_commuting_eq_refl (f : core (Fin 5) ≃+ core (Fin 5))
    (hf : ∀ g ∈ alternatingGroup (Fin 5), ∀ v,
      f (coreRepresentation (Fin 5) g v) = coreRepresentation (Fin 5) g (f v)) :
    f = AddEquiv.refl _ := by
  have hz : f (corePoint 0) = corePoint 0 := by
    have ha := (hf cycleA cycles_even.1 (corePoint 0)).symm
    have hb := (hf cycleB cycles_even.2 (corePoint 0)).symm
    rw [cycles_fix.1] at ha
    rw [cycles_fix.2] at hb
    rcases cycles_fixed (f (corePoint 0)) ha hb with h | h
    · have hn : corePoint 0 ≠ 0 := by
        intro he
        have := congrArg (fun u : core (Fin 5) => u.val 1) he
        exact one_ne_zero this
      exact False.elim (hn (f.injective (h.trans (map_zero f).symm)))
    · exact h
  have hp (i : Fin 5) : f (corePoint i) = corePoint i := by
    rw [← pointMover_apply i, hf _ (pointMover_even i), hz]
  apply AddEquiv.ext
  intro v
  rcases corePoint_generate v with rfl | ⟨i, rfl⟩ | ⟨i, j, rfl⟩
  · exact map_zero f
  · exact hp i
  · exact (map_add f _ _).trans (congrArg₂ (· + ·) (hp i) (hp j))

private theorem natural_commuting_eq_one
    (f : MulAut (Multiplicative (natural (Fin 5))))
    (hf : ∀ g ∈ alternatingGroup (Fin 5),
      f * naturalMulAction (Fin 5) g = naturalMulAction (Fin 5) g * f) : f = 1 := by
  let e := (coreEquivNatural (Fin 5) (by decide)).toAddEquiv
  let a := AddEquiv.toMultiplicative.symm f
  let F := e.trans (a.trans e.symm)
  have he (g : Equiv.Perm (Fin 5)) (v : core (Fin 5)) :
      e (coreRepresentation (Fin 5) g v) = naturalRepresentation (Fin 5) g (e v) :=
    coreEquivNatural_equivariant (Fin 5) (by decide) g v
  have hF : F = AddEquiv.refl _ := by
    apply core_commuting_eq_refl
    intro g hg v
    apply e.injective
    change e (e.symm (a (e (coreRepresentation (Fin 5) g v)))) =
      e (coreRepresentation (Fin 5) g (e.symm (a (e v))))
    rw [e.apply_symm_apply, he, he, e.apply_symm_apply]
    exact congrArg Multiplicative.toAdd
      (DFunLike.congr_fun (hf g hg) (Multiplicative.ofAdd (e v)))
  apply MulEquiv.ext
  intro v
  obtain ⟨w, hw⟩ := e.surjective v.toAdd
  have h := congrArg e (DFunLike.congr_fun hF w)
  change e (e.symm (a (e w))) = e w at h
  rw [e.apply_symm_apply, hw] at h
  exact congrArg Multiplicative.ofAdd h

/-- Every automorphism normalizing the natural alternating action in degree five
is induced by a coordinate permutation. -/
public theorem normalizer_alternatingFive_naturalMulAction_le_range :
    Subgroup.normalizer
      ((alternatingGroup (Fin 5)).map (naturalMulAction (Fin 5)) :
        Set (MulAut (Multiplicative (natural (Fin 5))))) ≤
      (naturalMulAction (Fin 5)).range := by
  intro f hf
  let j := naturalMulAction (Fin 5)
  let A := alternatingGroup (Fin 5)
  let B := A.map j
  let e : A ≃* B := A.equivMapOfInjective j
    (naturalMulAction_injective_of_odd (Fin 5) (by decide))
  let a : MulAut B := B.normalizerMonoidHom ⟨f, hf⟩
  let φ : MulAut A := e.trans (a.trans e.symm)
  obtain ⟨σ, hσ⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
      (by decide) (by decide)).surjective φ
  have hc : (j σ)⁻¹ * f = 1 := by
    apply natural_commuting_eq_one
    intro g hg
    have he : e (MulAut.conjNormal σ ⟨g, hg⟩) = a (e ⟨g, hg⟩) := by
      rw [hσ]
      exact e.apply_symm_apply _
    have hh := congrArg Subtype.val he
    change j (σ * g * σ⁻¹) = f * j g * f⁻¹ at hh
    rw [map_mul, map_mul, map_inv] at hh
    have hh' := (mul_inv_eq_iff_eq_mul.mp hh.symm)
    simpa only [mul_assoc, inv_mul_cancel_left] using congrArg ((j σ)⁻¹ * ·) hh'
  exact ⟨σ, inv_mul_eq_one.mp hc⟩

end BinaryPermutation
