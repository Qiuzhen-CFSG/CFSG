module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.Inputs
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.BinaryEndpoint
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.PSLTwoResidual
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms
public import Theory.GroupAction.AutomorphismFixerTransport
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.FieldClassical.LinearTwo.FieldFixer

/-!
# The intrinsic PSL₂ field-component fixer

An inner involution in binary PSL₂ has a two-group centralizer, which cannot
contain a component. Semilinear coverage and the cocycle calculation therefore
conjugate the given involution to an actual field involution. For n > 1 its
whole fixed subgroup is simple, so its embedded component equals that subgroup.
The same ambient equivalence transports the component to the fixed-field
subgroup, whose full automorphism fixer has order at most two.

The derived endpoint excludes n = 1 by `linearTwo_parameter_gt_one`; no
identification of PSL₂(2)′ with PSL₂(2) is made. The final theorem discharges
`ComponentFixerBound` without a field-action label or extra placement premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(4),
16.1.7(3a), and 16.3.5, printed pp.1171–1173 and 1178–1179 of
`refs/quasithin.pdf`.
-/

public section
open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open CFSG.Quasithin.Chapter16.CounterexampleGeometry.CoveredPersistence

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearTwo

private theorem component_forces_outer {K : Type*} [Field K] [Finite K] [CharP K 2]
    (a : MulAut (PSL2MatrixGroup K)) (ha : orderOf a = 2)
    (P : Subgroup (PSL2MatrixGroup K)) (hP : IsComponentIn P a.fixedSubgroup) :
    ¬ ∃ x, a = MulAut.conj x := by
  rintro ⟨x, rfl⟩
  have hx : orderOf x = 2 := by
    rw [← orderOf_injective MulAut.conj (conj_injective_of_center_eq_bot
      (BenderSuzuki.ZD.Linear.psl2_center_eq_bot (K := K))), ha]
  obtain ⟨g, t, ht, he, hB, hC⟩ := Theory.PSL2.involution_root_geometry x hx
  have htwo : IsPGroup 2 P := hC.to_le (by
    simpa only [MulAut.fixedSubgroup_conj] using hP.1)
  let := hP.quasisimple
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hP.ne_bot
  exact Group.IsPerfect.not_isNilpotent P htwo.isNilpotent

private theorem binary_fixed_simple {n : ℕ} (hn : 1 < n)
    (a : MulAut (PSL2BinaryMatrixGroup (2 * n))) (ha : orderOf a = 2)
    (houter : ¬ ∃ x, a = MulAut.conj x) : IsSimpleGroup a.fixedSubgroup := by
  obtain ⟨g, σ, he⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage (by omega) a
  have ha2 : a ^ 2 = 1 := by simpa only [ha] using pow_orderOf_eq_one a
  obtain ⟨m, hm, hnm, ⟨e⟩⟩ := BenderSuzuki.ZD.Linear.outer_fixed_model_of_semilinear
    (by omega) a ha2 g σ he houter
  have hmn : m = n := by omega
  subst m
  let : IsSimpleGroup (PSL2BinaryMatrixGroup n) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [BenderSuzuki.Converse.card_binaryGaloisField n (by omega)]
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 2 ≤ n))
  exact e.isSimpleGroup

/-- The component equals the whole fixed group, as an ambient subgroup. -/
theorem component_eq_fixed {n : ℕ} (hn : 1 < n)
    (a : MulAut (PSL2BinaryMatrixGroup (2 * n))) (ha : orderOf a = 2)
    (P : Subgroup (PSL2BinaryMatrixGroup (2 * n)))
    (hP : IsComponentIn P a.fixedSubgroup) : P = a.fixedSubgroup := by
  let := binary_fixed_simple hn a ha (component_forces_outer a ha P hP)
  rcases hP.2.1.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup a.fixedSubgroup) with hb | ht
  · have h := congrArg (Subgroup.map a.fixedSubgroup.subtype) hb
    rw [map_subgroupOf_eq_of_le hP.1, Subgroup.map_bot] at h
    exact (hP.ne_bot h).elim
  · exact le_antisymm hP.1 (subgroupOf_eq_top.mp ht)

private theorem exists_binary_model {S : Type*} [Group S] {n : ℕ} (hn : 0 < n)
    (hS : FieldFamily.linearTwo.ModelAt S (2 ^ (2 * n))) :
    Nonempty (S ≃* PSL2BinaryMatrixGroup (2 * n)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hS
  let : Fintype F := Fintype.ofFinite F
  let : Fintype (BinaryGaloisField (2 * n)) := Fintype.ofFinite _
  let f : F ≃+* BinaryGaloisField (2 * n) := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard,
      BenderSuzuki.Converse.card_binaryGaloisField (2 * n) (by omega)])
  exact ⟨e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv f)⟩

private theorem map_fixed {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : MulAut A) :
    a.fixedSubgroup.map e.toMonoidHom = (MulAut.congr e a).fixedSubgroup := by
  ext x
  rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
  change a (e.symm x) = e.symm x ↔ e (a (e.symm x)) = x
  rw [← e.apply_symm_apply x, e.injective.eq_iff]
  simp only [e.symm_apply_apply]

/-- One ambient equivalence carries the field action to the given involution
and its whole fixed subgroup onto the specified embedded component. -/
theorem exists_marked_field_model {S : Type*} [Group S] {n : ℕ} (hn : 1 < n)
    (hS : FieldFamily.linearTwo.ModelAt S (2 ^ (2 * n)))
    (a : MulAut S) (ha : orderOf a = 2) (P : Subgroup S)
    (hP : IsComponentIn P a.fixedSubgroup) :
    ∃ σ : BinaryGaloisField (2 * n) ≃+* BinaryGaloisField (2 * n),
      orderOf σ = 2 ∧ ∃ e : PSL2BinaryMatrixGroup (2 * n) ≃* S,
        MulAut.congr e (BenderSuzuki.ZD.Linear.fieldAut σ) = a ∧
        (BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup.map e.toMonoidHom = P := by
  obtain ⟨d⟩ := exists_binary_model (n := n) (by omega) hS
  let b : MulAut (PSL2BinaryMatrixGroup (2 * n)) := MulAut.congr d a
  have hb : orderOf b = 2 := by
    change orderOf (MulAut.congr d a) = 2
    exact ((MulAut.congr d).orderOf_eq a).trans ha
  have hQ : IsComponentIn (P.map d.toMonoidHom) b.fixedSubgroup := by
    have h := hP.map d
    rw [map_fixed] at h
    exact h
  have hout := component_forces_outer (K := BinaryGaloisField (2 * n)) b hb _ hQ
  have hPb := component_eq_fixed hn b hb _ hQ
  obtain ⟨g, σ, hsem⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage (by omega) b
  have hb2 : b ^ 2 = 1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hsq : (MulAut.conj g * BenderSuzuki.ZD.Linear.fieldAut σ) ^ 2 = 1 := by
    rwa [← hsem]
  obtain ⟨hs, hg⟩ := BenderSuzuki.ZD.Linear.semilinear_involution_data σ g hsq
  have hne : σ ≠ RingEquiv.refl _ := by
    intro h
    apply hout
    exact ⟨g, by rw [hsem, h, BenderSuzuki.ZD.Linear.fieldAut_refl, mul_one]⟩
  have hσ : orderOf σ = 2 := orderOf_eq_prime (by ext x; exact hs x) hne
  obtain ⟨c, hcoc⟩ := BenderSuzuki.ZD.Linear.semilinear_coboundary σ hs hne g hg
  have hc : MulAut.congr (MulAut.conj c) (BenderSuzuki.ZD.Linear.fieldAut σ) = b :=
    (BenderSuzuki.ZD.Linear.semilinear_congr_of_coboundary σ g c hcoc).trans hsem.symm
  let e : PSL2BinaryMatrixGroup (2 * n) ≃* S := (MulAut.conj c).trans d.symm
  have he : MulAut.congr e (BenderSuzuki.ZD.Linear.fieldAut σ) = a := by
    apply (MulAut.congr d).injective
    have h : MulAut.congr d (MulAut.congr e (BenderSuzuki.ZD.Linear.fieldAut σ)) =
        MulAut.congr (MulAut.conj c) (BenderSuzuki.ZD.Linear.fieldAut σ) := by
      ext x
      change d (d.symm (MulAut.conj c (BenderSuzuki.ZD.Linear.fieldAut σ
        ((MulAut.conj c).symm (d (d.symm x)))))) = _
      simp only [d.apply_symm_apply]
      rfl
    exact h.trans hc
  refine ⟨σ, hσ, e, he, ?_⟩
  rw [map_fixed, he]
  apply Subgroup.map_injective (f := d.toMonoidHom) d.injective
  rw [map_fixed]
  exact hPb.symm

universe u

/-- The intrinsic linear-two field-component bound, uniformly in the universe
of the ambient group and including every automorphism in the pointwise fixer. -/
theorem componentFixerBound : ComponentFixerBound.{u} FieldFamily.linearTwo := by
  intro S hS hfin hsimple hperfect n hn hmodel a ha P hP _hZ hsmall
  let : IsQuasisimple P := hP.quasisimple
  have hn' : 1 < n := linearTwo_parameter_gt_one hn hsmall
  obtain ⟨σ, hσ, e, _he, hPmap⟩ := exists_marked_field_model hn' hmodel a ha P hP
  have hc := FieldFixer.card_fixing_fixedSubgroup_le_two σ hσ
  have hcard := MulAut.card_fixingSubgroup_map e (BenderSuzuki.ZD.Linear.fieldAut σ).fixedSubgroup
  rw [hPmap] at hcard
  rw [hcard]
  exact lt_of_le_of_lt hc (by decide)

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical.LinearTwo
