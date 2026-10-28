module

public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.Intertwiner
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Extension.OddNormalizer
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.FieldTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugateBounds.Five.OuterModel.Maximality
public import Theory.SpecificGroups.SU3.OddInvolutionNormalization
public import Theory.SpecificGroups.SU3.OuterSolvable
public import Theory.GroupTheory.InvolutoryExtension

/-!
# From an odd projective normalizer to the marked S₇ extension

A unitary Frobenius twist inducing any odd permutation on an embedded A₇
can be corrected by an even permutation to induce `(01)(23)(45)`. Its
square is inner: the matrix norm is special unitary by the determinant norm
identity. It fixes A₇ pointwise, whose centralizer is trivial by maximality
and the trivial center of A₇. Thus the corrected twist is an involution.

The compatible two-coset construction extends the inner A₇ action faithfully
to S₇. The twist is outer because A₇ is self-normalizing in the inherited
simple PSU₃(5). Odd-prime involution normalization, followed by the marked
field/form transport, gives the literal equality with `concreteActor`.
Every calculation uses the actual projective matrix image and its scalar kernel.

The explicit matrix construction in `Extension.OddNormalizer` supplies the odd
projective normalizer. The final `concrete_extension` therefore proves the
specified `ConcreteExtension` contract, with inherited simplicity and the
existence of an actual A₇ embedding as its only hypotheses.
Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
manuscript pp.10–11.
-/

public noncomputable section
open Equiv Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem tripleSwap_sq : tripleSwap * tripleSwap = 1 := by decide +kernel

private theorem tripleSwap_odd : tripleSwap ∉ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup]
  decide +kernel

private theorem conj_injective [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j) :
    Function.Injective (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).ker.Normal).eq_bot_or_eq_top
    with h | h
  · exact h
  · let q : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 2, by
      rw [Perm.mem_alternatingGroup]; decide +kernel⟩
    let r : alternatingGroup (Fin 7) := ⟨swap 1 2 * swap 2 3, by
      rw [Perm.mem_alternatingGroup]; decide +kernel⟩
    have hc : MulAut.conj (j q) = 1 :=
      show j q ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).ker from h ▸ mem_top _
    have hh := DFunLike.congr_fun hc (j r)
    change j q * j r * (j q)⁻¹ = j r at hh
    have hqr : q * r = r * q := hj (by
      simpa only [map_mul] using (mul_inv_eq_iff_eq_mul.mp hh))
    exact False.elim ((by decide +kernel : q * r ≠ r * q) hqr)

private theorem alternating_maximal [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j) :
    IsCoatom j.range := by
  obtain ⟨e⟩ := exists_concrete_equiv_standard
  let : IsSimpleGroup StandardGroup := e.symm.isSimpleGroup
  have h := alternatingSeven_range_isCoatom (e.toMonoidHom.comp j) (e.injective.comp hj)
  rw [MonoidHom.range_comp] at h
  exact (e.mapSubgroup.isCoatom_iff j.range).mp h

private theorem alternating_normalizer [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j) :
    normalizer (j.range : Set ConcreteGroup) = j.range := by
  have hm := alternating_maximal j hj
  by_contra hn
  have htop : normalizer (j.range : Set ConcreteGroup) = ⊤ :=
    hm.2 _ (lt_of_le_of_ne j.range.le_normalizer (Ne.symm hn))
  have hnormal := normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · let q : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 1 2, by
      rw [Perm.mem_alternatingGroup]; decide +kernel⟩
    have hjq : j q = 1 := (mem_bot.mp (hbot ▸ (show j q ∈ j.range from ⟨q, rfl⟩)))
    have hq : q = 1 := hj (hjq.trans (map_one j).symm)
    exact (by decide +kernel : q ≠ 1) hq
  · exact hm.1 htop

private theorem intertwiner_not_embedded_inner
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j)
    (a : MulAut ConcreteGroup) (ha : ∀ q, a (j q) = j (tripleSwapAction q)) :
    ∀ q, a ≠ MulAut.conj (j q) := by
  intro q hq
  have he : (MulAut.conjNormal tripleSwap : MulAut (alternatingGroup (Fin 7))) =
      MulAut.conjNormal (q : Perm (Fin 7)) := by
    apply MulEquiv.ext
    intro r
    apply hj
    change j (tripleSwapAction r) = j ((MulAut.conjNormal (q : Perm (Fin 7))) r)
    rw [← ha, hq]
    change j q * j r * (j q)⁻¹ = j (q * r * q⁻¹)
    simp only [map_mul, map_inv]
  have heq := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 7 (by decide) he
  exact tripleSwap_odd (heq ▸ q.property)

private theorem intertwiner_outer [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j)
    (a : MulAut ConcreteGroup) (ha : ∀ q, a (j q) = j (tripleSwapAction q)) :
    ¬ ∃ s, a = MulAut.conj s := by
  rintro ⟨s, hs⟩
  have hnorm : s ∈ normalizer (j.range : Set ConcreteGroup) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨tripleSwapAction q, (ha q).symm.trans (by rw [hs]; rfl)⟩
    · intro hx
      obtain ⟨q, hq⟩ := hx
      obtain ⟨r, rfl⟩ := tripleSwapAction.surjective q
      refine ⟨r, ?_⟩
      apply a.injective
      rw [ha, hq, hs]
      rfl
  rw [alternating_normalizer j hj] at hnorm
  obtain ⟨q, rfl⟩ := hnorm
  exact intertwiner_not_embedded_inner j hj a ha q hs

/-- A compatible involution extends the actual inner A₇ action faithfully to S₇. -/
theorem symmetric_extension_of_intertwiner [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j)
    (a : MulAut ConcreteGroup) (ha2 : a ^ 2 = 1)
    (ha : ∀ q, a (j q) = j (tripleSwapAction q)) :
    ∃ f : Perm (Fin 7) →* MulAut ConcreteGroup,
      Function.Injective f ∧
      (∀ q : alternatingGroup (Fin 7), f q = MulAut.conj (j q)) ∧
      f tripleSwap = a := by
  let i := (alternatingGroup (Fin 7)).subtype
  let c : alternatingGroup (Fin 7) →* MulAut ConcreteGroup := MulAut.conj.comp j
  have hi : Function.Injective i := Subtype.val_injective
  have ht : tripleSwap ∉ i.range := by simpa [i] using tripleSwap_odd
  have hia (q : alternatingGroup (Fin 7)) :
      tripleSwap * i q = i (tripleSwapAction q) * tripleSwap := by
    change tripleSwap * (q : Perm (Fin 7)) =
      (tripleSwap * (q : Perm (Fin 7)) * tripleSwap⁻¹) * tripleSwap
    simp only [inv_mul_cancel_right]
  have hca (q : alternatingGroup (Fin 7)) : a * c q = c (tripleSwapAction q) * a := by
    apply MulEquiv.ext
    intro x
    change a (j q * x * (j q)⁻¹) = j (tripleSwapAction q) * a x * (j (tripleSwapAction q))⁻¹
    rw [map_mul, map_mul, map_inv, ha]
  have hs : a * a = 1 := by simpa only [pow_two] using ha2
  have hc : Function.Injective c := (conj_injective j hj).comp hj
  have hac : a ∉ c.range := by
    rintro ⟨q, hq⟩
    exact intertwiner_not_embedded_inner j hj a ha q hq.symm
  let L := i.range ⊔ zpowers tripleSwap
  have hL : L = ⊤ := by
    apply top_unique
    intro q _
    by_cases hq : q ∈ alternatingGroup (Fin 7)
    · exact mem_sup_left ⟨⟨q, hq⟩, rfl⟩
    · have hqt : q * tripleSwap⁻¹ ∈ alternatingGroup (Fin 7) := by
        rw [(alternatingGroup (Fin 7)).mul_mem_iff_of_index_two
          alternatingGroup.index_eq_two, inv_mem_iff]
        simp only [hq, tripleSwap_odd]
      have hprod : (q * tripleSwap⁻¹) * tripleSwap ∈ L :=
        L.mul_mem (mem_sup_left ⟨⟨_, hqt⟩, rfl⟩) (mem_sup_right (mem_zpowers _))
      simpa only [inv_mul_cancel_right] using hprod
  let e : Perm (Fin 7) →* L := (MonoidHom.id _).codRestrict _ (fun q => hL ▸ mem_top q)
  let g := InvolutoryExtension.lift i c tripleSwap a tripleSwapAction
    tripleSwap_sq hs hia hca hi ht
  refine ⟨g.comp e, ?_, ?_, ?_⟩
  · exact (InvolutoryExtension.lift_injective i c tripleSwap a tripleSwapAction
      tripleSwap_sq hs hia hca hi ht hc hac).comp (fun _ _ h => congrArg Subtype.val h)
  · intro q
    exact InvolutoryExtension.lift_block i c tripleSwap a tripleSwapAction
      tripleSwap_sq hs hia hca hi ht q
  · exact InvolutoryExtension.lift_graph i c tripleSwap a tripleSwapAction
      tripleSwap_sq hs hia hca hi ht

/-- Normalize the compatible outer involution to the specified entrywise actor.
The resulting equality concerns the triple transposition itself. -/
theorem marked_extension_of_intertwiner [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j)
    (a : MulAut ConcreteGroup) (ha2 : a ^ 2 = 1)
    (ha : ∀ q, a (j q) = j (tripleSwapAction q)) :
    ∃ f : Perm (Fin 7) →* MulAut ConcreteGroup,
      Function.Injective f ∧
      (∀ q : alternatingGroup (Fin 7),
        f (q : Perm (Fin 7)) ∈ (MulAut.conj : ConcreteGroup →* MulAut ConcreteGroup).range) ∧
      f tripleSwap = concreteActor := by
  obtain ⟨f, hf, heven, hmark⟩ := symmetric_extension_of_intertwiner j hj a ha2 ha
  have hcard : Nat.card (GaloisField 5 (2 * 1)) = 5 ^ 2 :=
    GaloisField.card 5 (2 * 1) (by decide)
  have hfixed : Nat.card {x : GaloisField 5 (2 * 1) // concreteForm.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      concreteForm.conj 5 1 (by decide) (by simpa only [pow_one] using hcard)
      (by simpa only [pow_one] using concreteForm_conj)
  obtain ⟨J, e, hconj, hform, hgraph⟩ := OddInvolutionNormalization.normalized_outer
    concreteForm (by decide : Nat.Prime 5) (by decide : Odd 5) hcard hfixed a ha2
    (intertwiner_outer j hj a ha)
  obtain ⟨d, hd⟩ := exists_marked_equiv J hcard (by rw [hconj]; exact concreteForm_conj)
    hform (MulAut.congr e a) hgraph
  let c := (MulAut.congr d).toMonoidHom.comp (MulAut.congr e).toMonoidHom
  refine ⟨c.comp f, ((MulAut.congr d).injective.comp (MulAut.congr e).injective).comp hf,
    ?_, ?_⟩
  · intro q
    refine ⟨d (e (j q)), ?_⟩
    change MulAut.conj (d (e (j q))) = MulAut.congr d (MulAut.congr e (f q))
    rw [heven, MulAut.congr_conj, MulAut.congr_conj]
  · change MulAut.congr d (MulAut.congr e (f tripleSwap)) = concreteActor
    rw [hmark, hd]

private theorem twist_square_inner (u : concreteForm.unitarySubgroup) :
    ∃ s : ConcreteGroup, (concreteForm.unitaryConj u * concreteActor) ^ 2 = MulAut.conj s := by
  have hform : concreteForm.form.map concreteForm.conj = concreteForm.form := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [concreteForm, OddPrimeSylow.NormalizedOuter.FormTransport.standardForm]
  let v : concreteForm.unitarySubgroup :=
    ⟨Matrix.GeneralLinearGroup.map concreteForm.conj.toRingHom u.val, by
      rw [mem_unitarySubgroup_iff]
      change concreteForm.conjTranspose (u.val.val.map concreteForm.conj) * concreteForm.form *
        (u.val.val.map concreteForm.conj) = concreteForm.form
      have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) (GaloisField 5 (2 * 1)) =>
        A.map concreteForm.conj) ((concreteForm.mem_unitarySubgroup_iff u.val).mp u.property)
      have hadj : (concreteForm.conjTranspose u.val.val).map concreteForm.conj =
          concreteForm.conjTranspose (u.val.val.map concreteForm.conj) := by
        ext i j
        rfl
      simpa only [RingEquiv.mapMatrix_apply, Matrix.map_mul, hadj, hform] using h⟩
  let n : concreteForm.specialSubgroup := ⟨(u * v).val, (u * v).property, by
    apply Units.ext
    change (u.val.val * u.val.val.map concreteForm.conj).det = 1
    rw [Matrix.det_mul, show (u.val.val.map concreteForm.conj).det =
      concreteForm.conj u.val.val.det from (concreteForm.conj.map_det _).symm]
    simpa only [mul_comm] using concreteForm.unitary_det_norm_one u⟩
  refine ⟨concreteForm.specialToProjective n, ?_⟩
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (concreteForm.unitaryConj u
    (concreteActor (concreteForm.unitaryConj u (concreteActor x)))).val =
      ((MulAut.conj (concreteForm.specialToProjective n)) x).val
  have hγγ : concreteActor (concreteActor x) = x :=
    DFunLike.congr_fun concreteActor_entrywise.sq_eq_one x
  rw [unitaryConj_apply_val, IsEntrywiseConjugation.apply_val concreteForm concreteActor_entrywise,
    unitaryConj_apply_val, map_mul, map_mul, map_inv]
  rw [← IsEntrywiseConjugation.apply_val concreteForm concreteActor_entrywise,
    hγγ, Matrix.ProjGenLinGroup.map_mk]
  change _ = (concreteForm.specialToProjective n).val * x.val *
    ((concreteForm.specialToProjective n).val)⁻¹
  rw [specialToProjective_apply_val]
  change _ = Matrix.ProjGenLinGroup.mk
    (u.val * Matrix.GeneralLinearGroup.map concreteForm.conj.toRingHom u.val) * x.val *
    (Matrix.ProjGenLinGroup.mk
      (u.val * Matrix.GeneralLinearGroup.map concreteForm.conj.toRingHom u.val))⁻¹
  rw [map_mul]
  group

private theorem alternating_centralizer [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j) :
    centralizer (j.range : Set ConcreteGroup) = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro s hs
  have hn := centralizer_le_normalizer (j.range : Set ConcreteGroup) hs
  rw [alternating_normalizer j hj] at hn
  obtain ⟨q, rfl⟩ := hn
  have hq : q ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff]
    intro r
    apply hj
    simpa only [map_mul] using (mem_centralizer_iff.mp hs (j r) ⟨r, rfl⟩)
  rw [alternatingGroup.center_eq_bot (by simp)] at hq
  rw [mem_bot.mp hq, map_one]

/-- A unitary Frobenius twist implementing the triple transposition is automatically
involutory; no scalar-norm or order hypothesis is required. -/
theorem semilinear_intertwiner_sq [IsSimpleGroup ConcreteGroup]
    (j : alternatingGroup (Fin 7) →* ConcreteGroup) (hj : Function.Injective j)
    (u : concreteForm.unitarySubgroup)
    (ha : ∀ q, (concreteForm.unitaryConj u * concreteActor) (j q) = j (tripleSwapAction q)) :
    (concreteForm.unitaryConj u * concreteActor) ^ 2 = 1 := by
  obtain ⟨s, hs⟩ := twist_square_inner u
  have hσ : ∀ q, tripleSwapAction (tripleSwapAction q) = q := by
    intro q
    have h := congrArg (MulAut.conjNormal (H := alternatingGroup (Fin 7))) tripleSwap_sq
    have hh := DFunLike.congr_fun h q
    simpa only [map_mul, map_one, MulAut.mul_apply, MulAut.one_apply, tripleSwapAction] using hh
  have hc : s ∈ centralizer (j.range : Set ConcreteGroup) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨q, rfl⟩
    have h := DFunLike.congr_fun hs (j q)
    change (concreteForm.unitaryConj u * concreteActor)
      ((concreteForm.unitaryConj u * concreteActor) (j q)) = s * j q * s⁻¹ at h
    rw [ha, ha, hσ] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  rw [alternating_centralizer j hj, mem_bot] at hc
  rw [hs, hc, map_one]

/-- Correct any odd permutation by an even one, using a special-unitary lift
of its embedded image. This uses multiplication, not S₇ conjugacy. -/
theorem correct_odd_semilinear_intertwiner
    (j : alternatingGroup (Fin 7) →* ConcreteGroup)
    (u : concreteForm.unitarySubgroup) (r : Perm (Fin 7))
    (hr : r ∉ alternatingGroup (Fin 7))
    (hact : ∀ q, (concreteForm.unitaryConj u * concreteActor) (j q) =
      j ((MulAut.conjNormal r) q)) :
    ∃ v : concreteForm.unitarySubgroup,
      ∀ q, (concreteForm.unitaryConj v * concreteActor) (j q) = j (tripleSwapAction q) := by
  have hqr : tripleSwap * r⁻¹ ∈ alternatingGroup (Fin 7) := by
    rw [(alternatingGroup (Fin 7)).mul_mem_iff_of_index_two
      alternatingGroup.index_eq_two, inv_mem_iff]
    simp only [tripleSwap_odd, hr]
  let q : alternatingGroup (Fin 7) := ⟨tripleSwap * r⁻¹, hqr⟩
  obtain ⟨x, hx⟩ := concreteForm.specialToProjective_surjective (j q)
  let w : concreteForm.unitarySubgroup := ⟨x.val, x.property.1⟩
  have hw : concreteForm.unitaryConj w = MulAut.conj (j q) := by
    rw [← hx]
    exact concreteForm.unitaryConj_special_is_inner x
  have hwu : concreteForm.unitaryConj (w * u) = MulAut.conj (j q) * concreteForm.unitaryConj u := by
    rw [← unitaryConjHom_apply, map_mul, unitaryConjHom_apply, unitaryConjHom_apply, hw]
  have hqr' : (MulAut.conjNormal (q : Perm (Fin 7)) : MulAut (alternatingGroup (Fin 7))) *
      MulAut.conjNormal r = tripleSwapAction := by
    rw [← map_mul]
    change MulAut.conjNormal ((tripleSwap * r⁻¹) * r) = MulAut.conjNormal tripleSwap
    rw [inv_mul_cancel_right]
  refine ⟨w * u, ?_⟩
  intro b
  rw [hwu, mul_assoc, MulAut.mul_apply, hact]
  have h := DFunLike.congr_fun hqr' b
  rw [MulAut.mul_apply] at h
  rw [← h]
  change j q * j ((MulAut.conjNormal r) b) * (j q)⁻¹ =
    j (q * ((MulAut.conjNormal r) b) * q⁻¹)
  simp only [map_mul, map_inv]

/-- The sole remaining input is the concrete odd projective normalizer.
All order, faithfulness, innerness, and literal marking clauses are discharged here. -/
theorem concrete_extension_of_projective_odd_normalizer
    (h : ProjectiveOddNormalizer) : ConcreteExtension := by
  intro _ hj
  obtain ⟨j, u, r, hj, hr, hact⟩ := h hj
  obtain ⟨v, hv⟩ := correct_odd_semilinear_intertwiner j u r hr hact
  exact marked_extension_of_intertwiner j hj _ (semilinear_intertwiner_sq j hj v hv) hv

/-- The faithful S₇ action on the literal projective matrix group, with even
image inner and the triple transposition equal to the prescribed entrywise actor. -/
theorem concrete_extension : ConcreteExtension :=
  concrete_extension_of_projective_odd_normalizer projective_odd_normalizer

end BenderSuzuki.MatrixGroups.HermitianForm.InvolutionConjugateBounds.Five.Outer
