module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.LinearExtension.OuterData
public import Theory.SpecificGroups.PSL2.OuterSolvable.FieldAutomorphisms

/-!
# Independence of the choices in the linear circle extension

For a field of order 2^(6n), the two coefficient automorphisms of order
three are `circleField F n` and its inverse. The cyclic diagonal outer
image likewise has just two nonidentity classes, represented by any
noncube coefficient and its inverse. An arbitrary permitted GL₃
representative has the class of its determinant.

The first Frobenius fixes the field actor and inverts the diagonal class.
Thus either it or the identity conjugates the chosen mixed cyclic outer
subgroup to any permitted alternative. Restricting this conjugation to
the full preimages constructs multiplicative equivalences and carries
the original marked inner component onto its literal target copy.
The specializations cover both field choices and every noncube coefficient.

Source: Aschbacher--Smith, Notation A.3.16, printed p.51 (PDF p.62).
This proves choice independence; the nonsplitting argument belongs to the
parent assembly and its separate twisted-norm input.
-/

public section

open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Theory.GroupTheory.AutomorphismExtensionBorel
noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

private theorem cyclic_order_three_choices {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {x y : G} (hx : orderOf x = 3) (hy : orderOf y = 3) : y = x ∨ y = x⁻¹ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hx1 : x ≠ 1 := by intro h; simp [h] at hx
  have hy1 : y ≠ 1 := by intro h; simp [h] at hy
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy3 : y ^ 3 = 1 := hy ▸ pow_orderOf_eq_one y
  have hxx : x ≠ x⁻¹ := by
    intro h
    have h2 : x ^ 2 = 1 := by simpa only [pow_two] using (mul_eq_one_iff_eq_inv.mpr h)
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at hd
    norm_num at hd
  by_contra! h
  have hsub : ({1, x, x⁻¹, y} : Finset G) ⊆ {a ∈ (Finset.univ : Finset G) | a ^ 3 = 1} := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl | rfl
    · simp
    · exact hx3
    · simp [inv_pow, hx3]
    · exact hy3
  have hle := (Finset.card_le_card hsub).trans
    (IsCyclic.card_pow_eq_one_le (α := G) (n := 3) (by decide))
  simp [hx1, hxx, Ne.symm hx1, Ne.symm hy1,
    Ne.symm h.1, Ne.symm h.2] at hle

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every order-three coefficient automorphism is one of the two source choices. -/
theorem circleField_choices {n : ℕ} (hn : 0 < n) (hc : Nat.card F = 2 ^ (6 * n))
    (σ : F ≃+* F) (hσ : orderOf σ = 3) :
    σ = circleField F n ∨ σ = (circleField F n)⁻¹ := by
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  exact cyclic_order_three_choices (circleField_order hn hc) hσ

omit [CharP F 2] in
/-- Any two noncube coefficients represent equal or inverse diagonal outer classes. -/
theorem circleDiagonalOuter_choices (a b : Fˣ) (ha : Noncube a) (hb : Noncube b) :
    circleDiagonalOuter b = circleDiagonalOuter a ∨
      circleDiagonalOuter b = (circleDiagonalOuter a)⁻¹ := by
  let f := circleDiagonalOuter (F := F)
  let : IsCyclic f.range := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let x : f.range := f.rangeRestrict a
  let y : f.range := f.rangeRestrict b
  have hx : orderOf x = 3 := by rw [← orderOf_coe]; exact circleDiagonalOuter_order a ha
  have hy : orderOf y = 3 := by rw [← orderOf_coe]; exact circleDiagonalOuter_order b hb
  exact (cyclic_order_three_choices hx hy).imp (congrArg Subtype.val) (congrArg Subtype.val)

private theorem choice_preimage_map {M : Type*} [Group M]
    (D : Subgroup (MulAut.Outer M)) (c : MulAut M) :
    (outerPreimage D).map (MulAut.conj c).toMonoidHom =
      outerPreimage (D.map (MulAut.conj (QuotientGroup.mk' (MulAut.innerSubgroup M) c)).toMonoidHom) := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup M)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨q y, hy, by simp [q, MulAut.conj_apply]⟩
  · rintro ⟨y, hy, he⟩
    refine ⟨c⁻¹ * x * c, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    change q (c⁻¹ * x * c) ∈ D
    have he' : q c * y * (q c)⁻¹ = q x := he
    rw [map_mul, map_mul, map_inv, ← he']
    simp only [inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one]
    exact hy

private theorem choice_zpowers_inv_mul_inv {G : Type*} [Group G] {x y : G}
    (h : Commute x y) : zpowers (x⁻¹ * y⁻¹) = zpowers (x * y) := by
  rw [← _root_.mul_inv_rev, h.eq, zpowers_inv]

private theorem choice_frobenius_fixes_field (n : ℕ) :
    MulAut.conj (qOuter F (fieldAction F (frobeniusEquiv F 2)))
      (qOuter F (fieldAction F (circleField F n))) =
      qOuter F (fieldAction F (circleField F n)) := by
  have h := ((Commute.self_pow (frobeniusEquiv F 2) (2 * n)).map
    (fieldAction F)).map (qOuter F)
  simp only [MulAut.conj_apply, circleField]
  rw [h.eq, mul_inv_cancel_right]

/-- Both allowed field choices and every nontrivial diagonal class give
conjugate mixed cyclic subgroups in the literal outer quotient. -/
theorem linearCircle_choice_outer_conjugator {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) :
    ∃ c : MulAut PSL(3,F),
      (c = 1 ∨ c = fieldAction F (frobeniusEquiv F 2)) ∧
      (zpowers (qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a)).map
          (MulAut.conj (qOuter F c)).toMonoidHom =
        zpowers (qOuter F (fieldAction F σ) * qOuter F (linearConj F g)) := by
  have hd : qOuter F (linearConj F g) = circleDiagonalOuter (GeneralLinearGroup.det g) :=
    linearOuterAction_eq_circleDiagonal_det g
  rw [hd]
  have hmap :
      (zpowers (qOuter F (fieldAction F (circleField F n)) * circleDiagonalOuter a)).map
          (MulAut.conj (qOuter F (fieldAction F (frobeniusEquiv F 2)))).toMonoidHom =
        zpowers (qOuter F (fieldAction F (circleField F n)) * (circleDiagonalOuter a)⁻¹) := by
    rw [MonoidHom.map_zpowers, map_mul]
    change zpowers (MulAut.conj _ _ * MulAut.conj _ _) = _
    rw [choice_frobenius_fixes_field]
    congr 2
    exact frobenius_circleDiagonal_conj a
  have hcomm := circle_outer_commute n a
  rcases circleField_choices hn hc σ hσ with rfl | rfl <;>
    rcases circleDiagonalOuter_choices a (GeneralLinearGroup.det g) ha hg with hd | hd
  · exact ⟨1, Or.inl rfl, by simp [hd]⟩
  · exact ⟨fieldAction F (frobeniusEquiv F 2), Or.inr rfl, by simpa only [hd] using hmap⟩
  · refine ⟨fieldAction F (frobeniusEquiv F 2), Or.inr rfl, ?_⟩
    rw [hd, map_inv, map_inv, hmap]
    simpa only [inv_inv] using (choice_zpowers_inv_mul_inv hcomm.inv_left)
  · refine ⟨1, Or.inl rfl, ?_⟩
    simpa [hd, MonoidHom.map_zpowers] using (choice_zpowers_inv_mul_inv hcomm).symm

/-- The conjugating actor transports the entire A.3.16 preimage, not just
its quotient or a chosen supplement. -/
theorem linearCircle_choice_conjugator {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) :
    ∃ c : MulAut PSL(3,F),
      (c = 1 ∨ c = fieldAction F (frobeniusEquiv F 2)) ∧
      (linearCircle F n a).map (MulAut.conj c).toMonoidHom =
        outerPreimage (zpowers (qOuter F (fieldAction F σ) * qOuter F (linearConj F g))) := by
  obtain ⟨c, hc, he⟩ := linearCircle_choice_outer_conjugator hn hc a ha σ hσ g hg
  refine ⟨c, hc, ?_⟩
  change (outerPreimage (zpowers (qOuter F (fieldAction F (circleField F n)) *
    circleDiagonalOuter a))).map _ = _
  rw [choice_preimage_map, he]

private def choiceActor {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) : MulAut PSL(3,F) :=
  (linearCircle_choice_conjugator hn hc a ha σ hσ g hg).choose

/-- A multiplicative equivalence from the published circle group to the
literal full preimage associated with any permitted source choices. -/
def linearCircleChoiceEquiv {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) :
    linearCircle F n a ≃*
      outerPreimage (zpowers (qOuter F (fieldAction F σ) * qOuter F (linearConj F g))) :=
  ((MulAut.conj (choiceActor hn hc a ha σ hσ g hg)).subgroupMap _).trans
    (MulEquiv.subgroupCongr
      (linearCircle_choice_conjugator hn hc a ha σ hσ g hg).choose_spec.2)

/-- The equivalence is induced by either the identity or the first
Frobenius on the ambient automorphism group. -/
theorem linearCircleChoiceEquiv_realized {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) :
    ∃ c : MulAut PSL(3,F), (c = 1 ∨ c = fieldAction F (frobeniusEquiv F 2)) ∧
      ∀ x : linearCircle F n a,
        (linearCircleChoiceEquiv hn hc a ha σ hσ g hg x).val = c * x.val * c⁻¹ :=
  ⟨choiceActor hn hc a ha σ hσ g hg,
    (linearCircle_choice_conjugator hn hc a ha σ hσ g hg).choose_spec.1,
    fun _ => rfl⟩

/-- The transported marked component is exactly the target's original
subgroupOf copy of Inn(PSL₃). -/
theorem linearCircleChoiceEquiv_component {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a : Fˣ) (ha : Noncube a)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hg : Noncube (GeneralLinearGroup.det g)) :
    (linearCircleComponent F n a).map (linearCircleChoiceEquiv hn hc a ha σ hσ g hg).toMonoidHom =
      (MulAut.innerSubgroup PSL(3,F)).subgroupOf
        (outerPreimage (zpowers (qOuter F (fieldAction F σ) * qOuter F (linearConj F g)))) := by
  let e := linearCircleChoiceEquiv hn hc a ha σ hσ g hg
  obtain ⟨c, _, he⟩ := linearCircleChoiceEquiv_realized hn hc a ha σ hσ g hg
  have hnorm : (MulAut.innerSubgroup PSL(3,F)).Normal := inferInstance
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (e x).val ∈ MulAut.innerSubgroup PSL(3,F)
    rw [he]
    exact hnorm.conj_mem _ hx c
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change (e.symm y).val ∈ MulAut.innerSubgroup PSL(3,F)
    have hh : c * (e.symm y).val * c⁻¹ = y.val :=
      (he (e.symm y)).symm.trans (congrArg Subtype.val (e.apply_symm_apply y))
    have hh' := hnorm.conj_mem y.val hy c⁻¹
    rw [← hh] at hh'
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh'

/-- Changing the noncube coefficient in the published carrier gives an
isomorphism of the actual extensions. This specializes the field choice to
`circleField F n` and the matrix choice to `circleDiagonalGL b`. -/
def linearCircleCoefficientEquiv {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a b : Fˣ) (ha : Noncube a) (hb : Noncube b) :
    linearCircle F n a ≃* linearCircle F n b :=
  linearCircleChoiceEquiv hn hc a ha (circleField F n) (circleField_order hn hc)
    (circleDiagonalGL b) (by simpa only [circleDiagonalGL_det] using hb)

/-- The coefficient-change equivalence preserves the published marked
component, with no replacement of its embedding. -/
theorem linearCircleCoefficientEquiv_component {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a b : Fˣ) (ha : Noncube a) (hb : Noncube b) :
    (linearCircleComponent F n a).map
        (linearCircleCoefficientEquiv hn hc a b ha hb).toMonoidHom =
      linearCircleComponent F n b :=
  linearCircleChoiceEquiv_component hn hc a ha (circleField F n) (circleField_order hn hc)
    (circleDiagonalGL b) (by simpa only [circleDiagonalGL_det] using hb)

/-- The other order-three field choice also gives an equivalent extension,
for every noncube diagonal coefficient. -/
def linearCircleInverseFieldEquiv {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a b : Fˣ) (ha : Noncube a) (hb : Noncube b) :
    linearCircle F n a ≃*
      outerPreimage (zpowers (qOuter F (fieldAction F (circleField F n)⁻¹) *
        qOuter F (linearConj F (circleDiagonalGL b)))) :=
  linearCircleChoiceEquiv hn hc a ha (circleField F n)⁻¹
    (by rw [orderOf_inv]; exact circleField_order hn hc)
    (circleDiagonalGL b) (by simpa only [circleDiagonalGL_det] using hb)

/-- The inverse-field-choice equivalence carries the component onto the
literal inner subgroup in the alternate full preimage. -/
theorem linearCircleInverseFieldEquiv_component {n : ℕ} (hn : 0 < n)
    (hc : Nat.card F = 2 ^ (6 * n)) (a b : Fˣ) (ha : Noncube a) (hb : Noncube b) :
    (linearCircleComponent F n a).map
        (linearCircleInverseFieldEquiv hn hc a b ha hb).toMonoidHom =
      (MulAut.innerSubgroup PSL(3,F)).subgroupOf
        (outerPreimage (zpowers (qOuter F (fieldAction F (circleField F n)⁻¹) *
          qOuter F (linearConj F (circleDiagonalGL b))))) :=
  linearCircleChoiceEquiv_component hn hc a ha (circleField F n)⁻¹
    (by rw [orderOf_inv]; exact circleField_order hn hc)
    (circleDiagonalGL b) (by simpa only [circleDiagonalGL_det] using hb)

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
