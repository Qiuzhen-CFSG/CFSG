module
public import Theory.Alternating.theorem_5_2_1_2
public import Theory.SpecificGroups.SymmetricFourKernel

/-!
# Symmetric-four recognition from an A₃ chain

Three generating involutions with the adjacent cubic relations and commuting
end generators give a quotient of the type-A Coxeter group of rank three.
The existing type-A normal form bounds its order by 24; the adjacent swaps
surject onto S₄, so this presentation is S₄. Distinct end generators exclude
its normal Klein-four kernel. The resulting isomorphism records all three
specified generators and requires no finiteness hypothesis on the target.

This is the presentation step used for the literal local quotients in
Goldschmidt, “Automorphisms of trivalent graphs” (1980), (6.9) and (6.12).
-/

public section
namespace Theory.GroupTheory.SymmetricFourCoxeterRecognition
open Subgroup GLS3.Chapter5.SchurPresentation
private abbrev W := (CoxeterMatrix.A 3).Group
private def adjacent (i : Fin 3) : Equiv.Perm (Fin 4) := Equiv.swap i.castSucc i.succ
private theorem adjacent_liftable : (CoxeterMatrix.A 3).IsLiftable adjacent := by
  unfold CoxeterMatrix.IsLiftable
  decide +kernel
private noncomputable def projection : W →* Equiv.Perm (Fin 4) :=
  (CoxeterMatrix.A 3).toCoxeterSystem.lift ⟨adjacent, adjacent_liftable⟩
private theorem projection_simple (i : Fin 3) :
    projection ((CoxeterMatrix.A 3).simple i) = adjacent i :=
  (CoxeterMatrix.A 3).toCoxeterSystem.lift_apply_simple adjacent_liftable i
private theorem projection_surjective : Function.Surjective projection := by
  apply MonoidHom.mrange_eq_top.mp
  apply top_unique
  rw [← Equiv.Perm.mclosure_swap_castSucc_succ 3]
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ⟨(CoxeterMatrix.A 3).simple i, projection_simple i⟩
private theorem projection_bijective : Function.Bijective projection := by
  let : Finite W := TypeANormalForm.group_finite 3
  apply projection_surjective.bijective_of_nat_card_le
  exact (TypeANormalForm.natCard_group_le_factorial 3).trans_eq (by
    rw [Nat.card_perm, Nat.card_fin])
private noncomputable def presentationEquiv : W ≃* Equiv.Perm (Fin 4) :=
  MulEquiv.ofBijective projection projection_bijective

variable {G : Type*} [Group G]
private def generators (a b c : G) : Fin 3 → G := ![a,b,c]
private theorem generators_liftable (a b c : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : Commute a c) :
    (CoxeterMatrix.A 3).IsLiftable (generators a b c) := by
  have hba : (b * a) ^ 3 = 1 := by
    have hh := congrArg (fun x => a⁻¹ * x * a) hab
    simpa [pow_succ, mul_assoc] using hh
  have hcb : (c * b) ^ 3 = 1 := by
    have hh := congrArg (fun x => b⁻¹ * x * b) hbc
    simpa [pow_succ, mul_assoc] using hh
  have hac2 : (a * c) ^ 2 = 1 := by rw [hac.mul_pow, ha, hc, one_mul]
  have hca2 : (c * a) ^ 2 = 1 := by rw [hac.symm.mul_pow, hc, ha, one_mul]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simpa [CoxeterMatrix.A, generators, ← pow_two] using
      (by first | exact ha | exact hb | exact hc | exact hab | exact hba |
        exact hbc | exact hcb | exact hac2 | exact hca2)

private noncomputable def representation (a b c : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : Commute a c) :
    Equiv.Perm (Fin 4) →* G :=
  ((CoxeterMatrix.A 3).toCoxeterSystem.lift
    ⟨generators a b c, generators_liftable a b c ha hb hc hab hbc hac⟩).comp
      presentationEquiv.symm.toMonoidHom

private theorem representation_adjacent (a b c : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : Commute a c)
    (i : Fin 3) :
    representation a b c ha hb hc hab hbc hac (adjacent i) = generators a b c i := by
  rw [← projection_simple i]
  change (CoxeterMatrix.A 3).toCoxeterSystem.lift
    ⟨generators a b c, generators_liftable a b c ha hb hc hab hbc hac⟩
      (presentationEquiv.symm
        (presentationEquiv ((CoxeterMatrix.A 3).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A 3).toCoxeterSystem.lift_apply_simple
    (generators_liftable a b c ha hb hc hab hbc hac) i

/-- Three involutions with the A₃ relations generate S₄ if the two end
reflections remain distinct. The isomorphism preserves the specified generators. -/
theorem exists_marked_equiv (a b c : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : Commute a c)
    (hgen : closure ({a, b, c} : Set G) = ⊤) (hne : a ≠ c) :
    ∃ e : G ≃* Equiv.Perm (Fin 4),
      e a = Equiv.swap 0 1 ∧ e b = Equiv.swap 1 2 ∧ e c = Equiv.swap 2 3 := by
  let f := representation a b c ha hb hc hab hbc hac
  have hfa : f (Equiv.swap 0 1) = a := representation_adjacent a b c ha hb hc hab hbc hac 0
  have hfb : f (Equiv.swap 1 2) = b := representation_adjacent a b c ha hb hc hab hbc hac 1
  have hfc : f (Equiv.swap 2 3) = c := representation_adjacent a b c ha hb hc hab hbc hac 2
  have hinj : Function.Injective f :=
    Theory.SpecificGroups.SymmetricFourKernel.injective_of_swap_ne f (by simpa [hfa, hfc] using hne)
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    rw [← hgen]
    apply (closure_le _).mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨Equiv.swap 0 1, hfa⟩
    · exact ⟨Equiv.swap 1 2, hfb⟩
    · exact ⟨Equiv.swap 2 3, hfc⟩
  let e : Equiv.Perm (Fin 4) ≃* G := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he (x : Equiv.Perm (Fin 4)) : e x = f x := rfl
  refine ⟨e.symm, ?_, ?_, ?_⟩
  · apply e.injective
    simpa only [e.apply_symm_apply, he] using hfa.symm
  · apply e.injective
    simpa only [e.apply_symm_apply, he] using hfb.symm
  · apply e.injective
    simpa only [e.apply_symm_apply, he] using hfc.symm

/-- The unmarked recognition statement used for the source local quotients. -/
theorem nonempty_equiv (a b c : G)
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hc : c ^ 2 = 1)
    (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : Commute a c)
    (hgen : closure ({a, b, c} : Set G) = ⊤) (hne : a ≠ c) :
    Nonempty (G ≃* Equiv.Perm (Fin 4)) :=
  ⟨(exists_marked_equiv a b c ha hb hc hab hbc hac hgen hne).choose⟩

end Theory.GroupTheory.SymmetricFourCoxeterRecognition
