module

public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Certificates
public import Theory.Mathieu.M22.Properties.HexadExtension

/-!
# Exhausting the standard M22 involution centralizer

Fifteen certified words in the fixed-hexad stabilizer give distinct conjugates
of the standard involution. Multiplying them by the centralizer embeds fifteen
copies of the centralizer into the stabilizer of order 5760, bounding its order
by 384. The 384 distinct certified centralizing words therefore exhaust it.

For every element outside the pointwise kernel, a certified conjugate fails to
commute with it. This gives the intrinsic characterization used to prove that
the kernel is characteristic. All elements lie in the original degree-22 M22.

This is a local ingredient for Aschbacher--Smith 1.1.5(3)(f), printed p.502,
and 2.3.9(7)(f), printed pp.525--526; it does not assert either full source lemma.
-/

public section
namespace Sporadic.Mathieu.M22RepresentativeKernel
open Subgroup
open scoped Pointwise

private theorem conjugator_mem (i : Fin 15) :
    conjugator i ∈ MulAction.stabilizer M22 hexad := by
  apply MulAction.mem_stabilizer_finset'.mpr
  intro x hx
  change (conjugator i).val x ∈ hexad
  rw [conjugator, wordElement_apply]
  exact conjugator_fixes_hexad i x hx

private theorem conjugator_apply (i : Fin 15) (x : Fin 22) :
    (conjugator i).val x = conjugatorTable i x := by
  rw [conjugator, wordElement_apply, conjugator_word_table]

private theorem conjugator_inv_apply (i : Fin 15) (x : Fin 22) :
    ((conjugator i)⁻¹).val x = conjugatorInvTable i x := by
  apply (conjugator i).val.injective
  change (conjugator i).val ((conjugator i).val.symm x) = _
  rw [Equiv.apply_symm_apply, conjugator_apply, conjugator_table_inv]

private theorem conjugates_injective : Function.Injective (fun i : Fin 15 =>
    conjugator i * m22GeneratorAInM22 * (conjugator i)⁻¹) := by
  intro i j h
  apply conjugate_point_injective
  have he := congrArg (fun g : M22 => g.val (0 : Fin 22)) h
  change (conjugator i).val (m22GeneratorA (((conjugator i)⁻¹).val 0)) =
    (conjugator j).val (m22GeneratorA (((conjugator j)⁻¹).val 0)) at he
  have ha (a : Fin 22) : m22GeneratorA a = letterTable 0 a := letter_apply 0 a
  simpa only [conjugator_apply, conjugator_inv_apply, ha] using he

private noncomputable def cosetProduct (p : Fin 15 × C) : MulAction.stabilizer M22 hexad :=
  ⟨conjugator p.1 * p.2.val, (MulAction.stabilizer M22 hexad).mul_mem
    (conjugator_mem p.1) (by
      rw [← fixedPoints_eq_hexad]
      exact m22_centralizer_le_fixedPoints_stabilizer _ p.2.property)⟩

private theorem cosetProduct_injective : Function.Injective cosetProduct := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hxy : conjugator i * x.val = conjugator j * y.val := congrArg Subtype.val h
  have he : i = j := by
    apply conjugates_injective
    have hc (u : C) : u.val * m22GeneratorAInM22 * u.val⁻¹ = m22GeneratorAInM22 := by
      rw [mem_centralizer_singleton_iff.mp u.property]
      group
    have hconj (k : M22) (u : C) :
        (k * u.val) * m22GeneratorAInM22 * (k * u.val)⁻¹ =
          k * m22GeneratorAInM22 * k⁻¹ := by
      calc
        _ = k * (u.val * m22GeneratorAInM22 * u.val⁻¹) * k⁻¹ := by group
        _ = _ := by rw [hc]
    change conjugator i * m22GeneratorAInM22 * (conjugator i)⁻¹ =
      conjugator j * m22GeneratorAInM22 * (conjugator j)⁻¹
    rw [← hconj (conjugator i) x, hxy, hconj]
  subst j
  have he' : x = y := Subtype.ext (mul_left_cancel hxy)
  subst y
  rfl

theorem centralizer_card_le : Nat.card C ≤ 384 := by
  have h := Nat.card_le_card_of_injective cosetProduct cosetProduct_injective
  rw [Nat.card_prod, Nat.card_fin, m22Hexad_stabilizer_card hexad_mem] at h
  omega

theorem rowElement_apply (i : Fin 384) (x : Fin 22) :
    (rowElement i).val x = rowTable i x := by
  rw [rowElement, wordElement_apply, row_word_table]

theorem rowElement_inv_apply (i : Fin 384) (x : Fin 22) :
    ((rowElement i)⁻¹).val x = rowInvTable i x := by
  apply (rowElement i).val.injective
  change (rowElement i).val ((rowElement i).val.symm x) = _
  rw [Equiv.apply_symm_apply, rowElement_apply, row_table_inv]

private theorem mem_centralizer_of_apply (g : M22)
    (hg : ∀ x : Fin 22, g.val (m22GeneratorA x) = m22GeneratorA (g.val x)) :
    g ∈ centralizer ({m22GeneratorAInM22} : Set M22) := by
  apply mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simpa only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply,
    m22GeneratorAInM22] using hg x

noncomputable def rowCentralizer (i : Fin 384) : C :=
  ⟨rowElement i, mem_centralizer_of_apply _ (by
    intro x
    have ha (a : Fin 22) : m22GeneratorA a = letterTable 0 a := letter_apply 0 a
    simp only [rowElement_apply, ha]
    exact row_commutes i x)⟩

private theorem rowCentralizer_injective : Function.Injective rowCentralizer := by
  intro i j h
  apply row_key_injective
  have he := congrArg (fun g : C =>
    (g.val.val 0).val * 22 ^ 2 + (g.val.val 1).val * 22 + (g.val.val 2).val) h
  simpa only [rowCentralizer, rowElement_apply] using he

/-- The certified 384 words exhaust the actual centralizer. -/
theorem rowCentralizer_surjective : Function.Surjective rowCentralizer :=
  (rowCentralizer_injective.bijective_of_nat_card_le
    (by simpa only [Nat.card_fin] using centralizer_card_le)).2

/-- The standard involution centralizer in the degree-22 model has order 384. -/
theorem centralizer_card : Nat.card C = 384 := by
  have h := Nat.card_eq_of_bijective rowCentralizer
    ⟨rowCentralizer_injective, rowCentralizer_surjective⟩
  simpa only [Nat.card_fin] using h.symm

/-- Commuting with every conjugate detects the pointwise fixed-hexad kernel. -/
theorem mem_kernel_of_commutes_conjugates (x : C)
    (hx : ∀ y : C, x * (y * x * y⁻¹) = (y * x * y⁻¹) * x) :
    x.val ∈ m22HexadPointwiseKernel (m22FixedPoints m22GeneratorAInM22) := by
  obtain ⟨i, rfl⟩ := rowCentralizer_surjective x
  rcases row_outside i with hfix | hne
  · rw [fixedPoints_eq_hexad]
    apply (mem_m22HexadPointwiseKernel _ _).mpr
    intro a ha
    exact (rowElement_apply i a).trans (hfix a ha)
  · have he := congrArg (fun g : C => g.val.val (witnessPoint i))
      (hx (rowCentralizer (witnessRow i)))
    change (rowElement i).val ((rowElement (witnessRow i)).val
      ((rowElement i).val (((rowElement (witnessRow i))⁻¹).val (witnessPoint i)))) =
      (rowElement (witnessRow i)).val ((rowElement i).val
        (((rowElement (witnessRow i))⁻¹).val ((rowElement i).val (witnessPoint i)))) at he
    simp only [rowElement_apply, rowElement_inv_apply] at he
    exact False.elim (hne he)

end Sporadic.Mathieu.M22RepresentativeKernel
