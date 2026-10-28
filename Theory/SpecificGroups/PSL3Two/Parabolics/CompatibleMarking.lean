module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Compatible Sylow and parabolic markings for PSL₃(2)

In a group actually isomorphic to PSL₃(2), a proper non-two-group containing
an indicated Sylow two-subgroup is maximal. One isomorphism to SL₃(2) takes
that Sylow subgroup to the upper triangular subgroup and the indicated
parabolic to the line stabilizer. Under the same isomorphism, the other
maximal overgroup is the point stabilizer.

Sylow conjugacy first marks the upper triangular subgroup. The Bruhat
classification places each proper overgroup in one of the two parabolics;
the orders eight and 24 force a non-two-group overgroup to equal its
parabolic. Inverse transpose followed by reversal of the coordinate basis
interchanges the two parabolics while preserving the upper triangular
subgroup, so the marking can be oriented as required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, the opening parabolic step of 13.8.19, printed
p.953. This is the intrinsic group-theoretic input to that argument; the
source module and residual identifications belong to its application.
-/

@[expose] public section
namespace Matrix.PSL3Two

/-- Inverse transpose followed by conjugation by the matrix reversing the
standard basis. This exchanges the two ends of the standard incident flag. -/
def flagDuality : MulAut SL :=
  (BinaryLinear.OuterCyclic.graphSL 3).trans (MulAut.conj (Bruhat.perm 5))

private theorem reversal_inv : (Bruhat.perm 5)⁻¹ = Bruhat.perm 5 := by decide +kernel

private theorem reversal_transpose_entry (g : SL) (i j : Fin 3) :
    ((Bruhat.perm 5) * g.transpose * (Bruhat.perm 5)⁻¹).val i j =
      g.val (Fin.rev j) (Fin.rev i) := by
  rw [reversal_inv]
  change (((Bruhat.perm 5).val * g.val.transpose) * (Bruhat.perm 5).val) i j = _
  fin_cases i <;> fin_cases j <;>
    simp [Bruhat.perm, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Fin.rev]

/-- Duality sends the line stabilizer to the point stabilizer. -/
theorem flagDuality_mem_point (g : SL) :
    flagDuality g ∈ pointParabolicSL ↔ g ∈ lineParabolicSL := by
  change (MulAut.conj (Bruhat.perm 5)) g.transpose⁻¹ ∈ pointParabolicSL ↔ _
  rw [map_inv, Subgroup.inv_mem_iff, mem_pointParabolicSL_iff,
    mem_lineParabolicSL_iff]
  change ((Bruhat.perm 5) * g.transpose * (Bruhat.perm 5)⁻¹).val 1 0 = 0 ∧
    ((Bruhat.perm 5) * g.transpose * (Bruhat.perm 5)⁻¹).val 2 0 = 0 ↔ _
  simp only [reversal_transpose_entry]
  change g.val 2 1 = 0 ∧ g.val 2 0 = 0 ↔ _
  exact and_comm

/-- Duality sends the point stabilizer to the line stabilizer. -/
theorem flagDuality_mem_line (g : SL) :
    flagDuality g ∈ lineParabolicSL ↔ g ∈ pointParabolicSL := by
  change (MulAut.conj (Bruhat.perm 5)) g.transpose⁻¹ ∈ lineParabolicSL ↔ _
  rw [map_inv, Subgroup.inv_mem_iff, mem_lineParabolicSL_iff,
    mem_pointParabolicSL_iff]
  change ((Bruhat.perm 5) * g.transpose * (Bruhat.perm 5)⁻¹).val 2 0 = 0 ∧
    ((Bruhat.perm 5) * g.transpose * (Bruhat.perm 5)⁻¹).val 2 1 = 0 ↔ _
  simp only [reversal_transpose_entry]
  change g.val 2 0 = 0 ∧ g.val 1 0 = 0 ↔ _
  exact and_comm

/-- The point parabolic has exactly the line parabolic as its image. -/
theorem flagDuality_map_point : pointParabolicSL.map flagDuality.toMonoidHom =
    lineParabolicSL := by
  ext g
  obtain ⟨g, rfl⟩ := flagDuality.surjective g
  rw [flagDuality_mem_line]
  exact Subgroup.mem_map_iff_mem flagDuality.injective

/-- The line parabolic has exactly the point parabolic as its image. -/
theorem flagDuality_map_line : lineParabolicSL.map flagDuality.toMonoidHom =
    pointParabolicSL := by
  ext g
  obtain ⟨g, rfl⟩ := flagDuality.surjective g
  rw [flagDuality_mem_point]
  exact Subgroup.mem_map_iff_mem flagDuality.injective

/-- The same duality preserves the standard Sylow two-subgroup. -/
theorem flagDuality_map_borel : borelSL.map flagDuality.toMonoidHom = borelSL := by
  rw [borelSL, Subgroup.map_inf _ _ _ flagDuality.injective,
    flagDuality_map_point, flagDuality_map_line, inf_comm]

private theorem eq_of_borel_le_of_not_two (H K : Subgroup SL) (hBH : borelSL ≤ H)
    (hHK : H ≤ K) (hK : Nat.card K = 24) (hH : ¬ IsPGroup 2 H) : H = K := by
  have hd₁ := Subgroup.card_dvd_of_le hBH
  have hd₂ := Subgroup.card_dvd_of_le hHK
  rw [card_borelSL] at hd₁
  rw [hK] at hd₂
  have hb : Nat.card H ≤ 24 := Nat.le_of_dvd (by decide) hd₂
  have hc : Nat.card H = 8 ∨ Nat.card H = 24 := by
    have hn : Nat.card H ≠ 0 := Nat.card_pos.ne'
    have h16 : Nat.card H ≠ 16 := by intro h; norm_num [h] at hd₂
    omega
  rcases hc with hc | hc
  · exact (hH (IsPGroup.of_card (n := 3) hc)).elim
  · exact Subgroup.eq_of_le_of_card_ge hHK (by omega)

/-- Proper non-two-group overgroups of the standard Borel are precisely
its two parabolics; maximality need not be assumed. -/
theorem parabolic_of_borel_le_of_not_two (H : Subgroup SL) (hB : borelSL ≤ H)
    (hH : H ≠ ⊤) (h₂ : ¬ IsPGroup 2 H) :
    H = pointParabolicSL ∨ H = lineParabolicSL := by
  rcases overgroup_borelSL H hB hH with hp | hl
  · exact Or.inl (eq_of_borel_le_of_not_two H _ hB hp card_pointParabolicSL h₂)
  · exact Or.inr (eq_of_borel_le_of_not_two H _ hB hl card_lineParabolicSL h₂)

open scoped Pointwise

variable {A : Type*} [Group A] [Finite A]

/-- An actual projective model can be marked at any specified Sylow subgroup. -/
theorem exists_sylow_marking (e₀ : A ≃* PSL) (S : Sylow 2 A) :
    ∃ e : A ≃* SL, (S : Subgroup A).map e.toMonoidHom = borelSL := by
  let S₀ : Sylow 2 PSL := S.mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL S₀ borelSylow
  let c : A ≃* PSL := e₀.trans (MulAut.conj g)
  have hc : (S : Subgroup A).map c.toMonoidHom = borel := by
    change (S : Subgroup A).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom) = _
    rw [← Subgroup.map_map]
    change ((g • S₀ : Sylow 2 PSL) : Subgroup PSL) = borel
    rw [hg, coe_borelSylow]
  refine ⟨c.trans equiv.symm, ?_⟩
  change (S : Subgroup A).map (equiv.symm.toMonoidHom.comp c.toMonoidHom) = _
  rw [← Subgroup.map_map, hc]
  have hp : equiv.toMonoidHom = project := by ext x; exact equiv_apply x
  change (borelSL.map project).map equiv.symm.toMonoidHom = borelSL
  rw [← hp]
  exact equiv.mapSubgroup.symm_apply_apply borelSL

/-- Orient a single Sylow marking so the specified proper non-two-group
overgroup becomes the line stabilizer. -/
theorem exists_sylow_line_marking (e₀ : A ≃* PSL) (S : Sylow 2 A)
    (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P) (hP : P ≠ ⊤)
    (h₂ : ¬ IsPGroup 2 P) :
    ∃ e : A ≃* SL, (S : Subgroup A).map e.toMonoidHom = borelSL ∧
      P.map e.toMonoidHom = lineParabolicSL := by
  obtain ⟨e, hS⟩ := exists_sylow_marking e₀ S
  have hb : borelSL ≤ e.mapSubgroup P := by
    rw [← hS]
    exact e.mapSubgroup.monotone hSP
  have hp : e.mapSubgroup P ≠ ⊤ := by
    intro h
    exact hP (e.mapSubgroup.injective (h.trans e.mapSubgroup.map_top.symm))
  have hn : ¬ IsPGroup 2 (e.mapSubgroup P) := fun h =>
    h₂ (h.of_equiv (e.subgroupMap P).symm)
  rcases parabolic_of_borel_le_of_not_two _ hb hp hn with he | he
  · refine ⟨e.trans flagDuality, ?_, ?_⟩
    · change (S : Subgroup A).map (flagDuality.toMonoidHom.comp e.toMonoidHom) = _
      rw [← Subgroup.map_map, hS, flagDuality_map_borel]
    · change P.map (flagDuality.toMonoidHom.comp e.toMonoidHom) = _
      rw [← Subgroup.map_map]
      change (e.mapSubgroup P).map flagDuality.toMonoidHom = _
      rw [he, flagDuality_map_point]
  · exact ⟨e, hS, he⟩

/-- A proper non-two-group over a Sylow two-subgroup is maximal. There is
one equivalence marking this subgroup as the line parabolic, the other
maximal overgroup as the point parabolic, and their intersection as the
Borel. These are all the maximal overgroups of the specified Sylow subgroup. -/
theorem exists_compatible_parabolic_marking (e₀ : A ≃* PSL) (S : Sylow 2 A)
    (P : Subgroup A) (hSP : (S : Subgroup A) ≤ P) (hP : P ≠ ⊤)
    (h₂ : ¬ IsPGroup 2 P) :
    IsCoatom P ∧ ∃ (e : A ≃* SL) (Q : Subgroup A),
      (S : Subgroup A).map e.toMonoidHom = borelSL ∧
      P.map e.toMonoidHom = lineParabolicSL ∧
      Q.map e.toMonoidHom = pointParabolicSL ∧
      IsCoatom Q ∧ Q ≠ P ∧ (S : Subgroup A) ≤ Q ∧
      P ⊓ Q = (S : Subgroup A) ∧
      ∀ R : Subgroup A, IsCoatom R →
        ((S : Subgroup A) ≤ R ↔ R = P ∨ R = Q) := by
  obtain ⟨e, hS, heP⟩ := exists_sylow_line_marking e₀ S P hSP hP h₂
  let E := e.mapSubgroup
  let Q : Subgroup A := E.symm pointParabolicSL
  have hEP : E P = lineParabolicSL := heP
  have hES : E (S : Subgroup A) = borelSL := hS
  have hEQ : E Q = pointParabolicSL := E.apply_symm_apply _
  have hPc : IsCoatom P := (E.isCoatom_iff P).mp (hEP ▸ isCoatom_lineParabolicSL)
  have hQc : IsCoatom Q := (E.isCoatom_iff Q).mp (hEQ ▸ isCoatom_pointParabolicSL)
  have hQP : Q ≠ P := by
    intro h
    exact pointParabolicSL_ne_line (hEQ.symm.trans ((congrArg E h).trans hEP))
  have hSQ : (S : Subgroup A) ≤ Q := E.le_iff_le.mp (by
    rw [hES, hEQ]
    exact inf_le_left)
  refine ⟨hPc, e, Q, hS, heP, hEQ, hQc, hQP, hSQ, ?_, ?_⟩
  · apply E.injective
    rw [E.map_inf, hEP, hEQ, hES]
    exact inf_comm _ _
  · intro R hR
    constructor
    · intro hSR
      have hRc : IsCoatom (E R) := (E.isCoatom_iff R).mpr hR
      have hBR : borelSL ≤ E R := hES ▸ E.monotone hSR
      rcases (coatoms_over_borelSL (E R)).mp ⟨hRc, hBR⟩ with hr | hr
      · exact Or.inr (E.injective (hr.trans hEQ.symm))
      · exact Or.inl (E.injective (hr.trans hEP.symm))
    · rintro (rfl | rfl)
      · exact hSP
      · exact hSQ

end Matrix.PSL3Two
