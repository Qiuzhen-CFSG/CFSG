module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Theory.GroupTheory.IndexTwoExtensionEquivalence
public import GorensteinWalter.PSL2Center

/-!
# The quadratic-field extension of PSL₂(9)

The exceptional ten-point-action comparison identifies the three projective
matrix generators with two disjoint three-cycles and a double transposition in
A₆. Cubic Frobenius fixes the first and third generators and inverts the second.
Conjugation by the transposition (4 5) has precisely this action. Field transport
retains this identity over every field of order nine.

For an arbitrary index-two embedding with this specified outside action, the
outside lift squares into the component. Its square centralizes that component,
and hence is trivial. The index-two extension comparison then constructs S₆,
agreeing with the actual component embedding and the specified outside lift.
No splitting hypothesis or recognition from the group order is used.

Source application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, F.6.18(8), pp.309–310, and 15.4.18, p.1163.
The imported exceptional comparison and coordinates are the attributed ATLAS
port at revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917; their ATLAS Research
and Attribution License 1.0 is retained in the imported modules and LICENSES.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Atlas.Comparisons.Exceptional.NineFieldExtension
open Nine TriplePartitions

abbrev outside : Equiv.Perm (Fin 6) := Equiv.swap 4 5

private theorem equiv_upper : psl2NineCoordinatesEquivAlt6 (upperOne : PSL(2,F)) =
    firstCycle := by
  apply action_injective
  rw [psl2NineCoordinatesEquivAlt6_action, permutation_upper, action_firstCycle]

private theorem equiv_omega : psl2NineCoordinatesEquivAlt6 (upperOmega : PSL(2,F)) =
    secondCycle := by
  apply action_injective
  rw [psl2NineCoordinatesEquivAlt6_action, permutation_omega, action_secondCycle]

private theorem equiv_inversion :
    psl2NineCoordinatesEquivAlt6 (inversionMatrix : PSL(2,F)) = doubleSwap := by
  apply action_injective
  rw [psl2NineCoordinatesEquivAlt6_action, permutation_inversion, action_doubleSwap]

private theorem field_upper (σ : F ≃+* F) (hs : ∀ x, σ x = x ^ 3) :
    Atlas.fieldEquivPSL 2 σ (upperOne : PSL(2,F)) = (upperOne : PSL(2,F)) := by
  change Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ upperOne) = QuotientGroup.mk' _ upperOne
  rw [Atlas.fieldEquivPSL_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change σ (upperOne.val i j) = upperOne.val i j
  rw [hs]
  fin_cases i <;> fin_cases j <;> decide

private theorem field_omega (σ : F ≃+* F) (hs : ∀ x, σ x = x ^ 3) :
    Atlas.fieldEquivPSL 2 σ (upperOmega : PSL(2,F)) = (upperOmega : PSL(2,F))⁻¹ := by
  change Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ upperOmega) = (QuotientGroup.mk' _ upperOmega)⁻¹
  rw [Atlas.fieldEquivPSL_mk, ← map_inv]
  apply congrArg (QuotientGroup.mk' _)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change σ (upperOmega.val i j) = (upperOmega⁻¹).val i j
  rw [hs]
  fin_cases i <;> fin_cases j <;> decide

private theorem field_inversion (σ : F ≃+* F) (hs : ∀ x, σ x = x ^ 3) :
    Atlas.fieldEquivPSL 2 σ (inversionMatrix : PSL(2,F)) = (inversionMatrix : PSL(2,F)) := by
  change Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ inversionMatrix) = QuotientGroup.mk' _ inversionMatrix
  rw [Atlas.fieldEquivPSL_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change σ (inversionMatrix.val i j) = inversionMatrix.val i j
  rw [hs]
  fin_cases i <;> fin_cases j <;> decide

/-- Cubic Frobenius acts as the specified odd transposition on the marked A₆. -/
theorem coordinate_action (σ : F ≃+* F) (hs : ∀ x, σ x = x ^ 3)
    (x : PSL(2,F)) :
    (psl2NineCoordinatesEquivAlt6 (Atlas.fieldEquivPSL 2 σ x) : Equiv.Perm (Fin 6)) =
      outside * (psl2NineCoordinatesEquivAlt6 x : Equiv.Perm (Fin 6)) * outside⁻¹ := by
  let f := (alternatingGroup (Fin 6)).subtype.comp psl2NineCoordinatesEquivAlt6.toMonoidHom
  have hh : f.comp (Atlas.fieldEquivPSL 2 σ).toMonoidHom =
      (MulAut.conj outside).toMonoidHom.comp f := by
    apply MonoidHom.eq_of_eqOn_dense psl_generated
    intro g hg
    change (psl2NineCoordinatesEquivAlt6 (Atlas.fieldEquivPSL 2 σ g) : Equiv.Perm (Fin 6)) =
      outside * (psl2NineCoordinatesEquivAlt6 g : Equiv.Perm (Fin 6)) * outside⁻¹
    rcases hg with rfl | hg
    · rw [field_upper σ hs, equiv_upper]
      decide
    rcases hg with rfl | hg
    · rw [field_omega σ hs, map_inv, equiv_omega]
      decide
    have he : g = (inversionMatrix : PSL(2,F)) := Set.mem_singleton_iff.mp hg
    subst g
    rw [field_inversion σ hs, equiv_inversion]
    decide
  exact DFunLike.congr_fun hh x

/-- The actual component comparison, with field transport followed by the ten-point action. -/
noncomputable def componentEquiv {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) : PSL(2,K) ≃* alternatingGroup (Fin 6) :=
  (Atlas.fieldEquivPSL 2 (Nine.fieldEquiv hK)).trans psl2NineCoordinatesEquivAlt6

/-- Field transport intertwines Frobenius with the same marked transposition. -/
theorem componentEquiv_action {K : Type*} [Field K] [Finite K]
    (hK : Nat.card K = 9) (σ : K ≃+* K) (hs : ∀ x, σ x = x ^ 3)
    (x : PSL(2,K)) :
    (componentEquiv hK (Atlas.fieldEquivPSL 2 σ x) : Equiv.Perm (Fin 6)) =
      outside * (componentEquiv hK x : Equiv.Perm (Fin 6)) * outside⁻¹ := by
  let e := Nine.fieldEquiv hK
  let τ := e.symm.trans (σ.trans e)
  have ht (x : F) : τ x = x ^ 3 := by
    change e (σ (e.symm x)) = x ^ 3
    rw [hs, map_pow, e.apply_symm_apply]
  have hcompat : Atlas.fieldEquivPSL 2 e (Atlas.fieldEquivPSL 2 σ x) =
      Atlas.fieldEquivPSL 2 τ (Atlas.fieldEquivPSL 2 e x) := by
    induction x using QuotientGroup.induction_on with | H g =>
      change Atlas.fieldEquivPSL 2 e (Atlas.fieldEquivPSL 2 σ (QuotientGroup.mk' _ g)) =
        Atlas.fieldEquivPSL 2 τ (Atlas.fieldEquivPSL 2 e (QuotientGroup.mk' _ g))
      simp only [Atlas.fieldEquivPSL_mk]
      apply congrArg (QuotientGroup.mk' _)
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      change e (σ (g.val i j)) = e (σ (e.symm (e (g.val i j))))
      rw [e.symm_apply_apply]
  change (psl2NineCoordinatesEquivAlt6 (Atlas.fieldEquivPSL 2 e
    (Atlas.fieldEquivPSL 2 σ x)) : Equiv.Perm (Fin 6)) = _
  rw [hcompat]
  exact coordinate_action τ ht _

private theorem square_eq_one {M D : Type*} [Group M] [Group D]
    (hc : center M = ⊥) (a : MulAut M) (ha : ∀ x, a (a x) = x)
    (i : M →* D) (hi : Function.Injective i) (htwo : i.range.index = 2)
    (t : D) (hact : ∀ x, t * i x * t⁻¹ = i (a x)) : t ^ 2 = 1 := by
  obtain ⟨z, hz⟩ := i.range.sq_mem_of_index_two htwo t
  have hcomm (x : M) : t ^ 2 * i x * (t ^ 2)⁻¹ = i x := by
    calc
      t ^ 2 * i x * (t ^ 2)⁻¹ = t * (t * i x * t⁻¹) * t⁻¹ := by rw [pow_two]; group
      _ = i (a (a x)) := by rw [hact, hact]
      _ = i x := by rw [ha]
  have hzcent : z ∈ center M := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply hi
    simp only [map_mul]
    rw [hz]
    have hh := hcomm x
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hz1 : z = 1 := by simpa only [hc, mem_bot] using hzcent
  rw [← hz, hz1, map_one]

/-- A prescribed cubic Frobenius lift over a nine-element field extends the
actual exceptional component equivalence to the symmetric group. -/
theorem exists_equiv {K D : Type*} [Field K] [Finite K] [Group D]
    (hK : Nat.card K = 9) (σ : K ≃+* K) (hs : ∀ x, σ x = x ^ 3)
    (i : PSL(2,K) →* D) (hi : Function.Injective i) (htwo : i.range.index = 2)
    (t : D) (ht : t ∉ i.range)
    (hact : ∀ x, t * i x * t⁻¹ = i (Atlas.fieldEquivPSL 2 σ x)) :
    ∃ e : D ≃* Equiv.Perm (Fin 6),
      (∀ x, e (i x) = (componentEquiv hK x : Equiv.Perm (Fin 6))) ∧ e t = outside := by
  let c := componentEquiv hK
  let a := Atlas.fieldEquivPSL 2 σ
  have ha (x : PSL(2,K)) : a (a x) = x := by
    apply c.injective
    apply Subtype.ext
    change (componentEquiv hK (a (a x)) : Equiv.Perm (Fin 6)) = _
    rw [componentEquiv_action hK σ hs, componentEquiv_action hK σ hs]
    have hout : outside * outside = 1 := by decide
    calc
      outside * (outside * (componentEquiv hK x : Equiv.Perm (Fin 6)) * outside⁻¹) * outside⁻¹ =
          (outside * outside) * (componentEquiv hK x : Equiv.Perm (Fin 6)) *
            (outside * outside)⁻¹ := by group
      _ = _ := by rw [hout]; simp [c]
  have ht2 := square_eq_one (GorensteinWalter.psl2_center_eq_bot K) a ha i hi htwo t hact
  let eN : i.range ≃* alternatingGroup (Fin 6) := (MonoidHom.ofInjective hi).symm.trans c
  let : i.range.Normal := normal_of_index_eq_two htwo
  have hN (x : PSL(2,K)) : eN ⟨i x, ⟨x, rfl⟩⟩ = c x := by
    change c ((MonoidHom.ofInjective hi).symm ((MonoidHom.ofInjective hi) x)) = c x
    rw [MulEquiv.symm_apply_apply]
  have hNact (n : i.range) :
      (eN ⟨t * (n : D) * t⁻¹, (inferInstance : i.range.Normal).conj_mem n n.property t⟩ :
        Equiv.Perm (Fin 6)) = outside * (eN n : Equiv.Perm (Fin 6)) * outside⁻¹ := by
    obtain ⟨x, hx⟩ := n.property
    have hn : n = ⟨i x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    subst n
    have hm : (⟨t * i x * t⁻¹, (inferInstance : i.range.Normal).conj_mem
        (i x) ⟨x, rfl⟩ t⟩ : i.range) = ⟨i (a x), ⟨a x, rfl⟩⟩ := Subtype.ext (hact x)
    rw [hm, hN, hN]
    exact componentEquiv_action hK σ hs x
  have hNsq : (eN ⟨t ^ 2, i.range.sq_mem_of_index_two htwo t⟩ :
      Equiv.Perm (Fin 6)) = outside ^ 2 := by
    have he : (⟨t ^ 2, i.range.sq_mem_of_index_two htwo t⟩ : i.range) = 1 :=
      Subtype.ext ht2
    rw [he, map_one]
    decide
  obtain ⟨e, he, het⟩ := exists_mulEquiv_of_index_two_extensions i.range
    (alternatingGroup (Fin 6)) htwo alternatingGroup.index_eq_two t outside ht
    (by change Equiv.Perm.sign outside ≠ 1; decide) eN hNsq hNact
  refine ⟨e, fun x => ?_, het⟩
  exact (he ⟨i x, ⟨x, rfl⟩⟩).trans (congrArg Subtype.val (hN x))

end Atlas.Comparisons.Exceptional.NineFieldExtension
