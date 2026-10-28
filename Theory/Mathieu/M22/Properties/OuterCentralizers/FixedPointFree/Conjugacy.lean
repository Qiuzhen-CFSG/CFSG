module

public import Theory.Mathieu.M22.Properties.OuterCentralizers.FixedPointFree.ConjugacyData
import all Theory.Mathieu.M22.Properties.CubicInverters.Enumeration

/-!
# Conjugacy of fixed-point-free M₂₂ design involutions

Sylow conjugacy moves an arbitrary involution into the already certified
256-element Sylow subgroup. The finite word certificate then conjugates
each fixed-point-free row to the marked representative. Conjugation in
the design group induces an actual isomorphism of the full centralizers
in M₂₂, preserving their original ambient embeddings.

The internal import exposes only the implementation equation of `rowSylow`
needed to use its existing surjectivity theorem; the shared module is unchanged.

Source: the fixed-point-free branch of Aschbacher–Smith 16.1.5(5), p.1171.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
open Subgroup M22CubicInverters
open scoped Pointwise

private theorem moves_of_card_zero (s : m22DesignAut)
    (h : (fixedPoints s).card = 0) (x : Fin 22) : s.val x ≠ x := by
  intro hx
  have hm := (mem_fixedPoints s x).mpr hx
  rw [Finset.card_eq_zero.mp h] at hm
  exact Finset.notMem_empty x hm

private theorem moves_conj (g s : m22DesignAut)
    (h : ∀ x : Fin 22, s.val x ≠ x) (x : Fin 22) :
    (MulAut.conj g s).val x ≠ x := by
  intro hx
  apply h (g.val⁻¹ x)
  have hy := congrArg (fun y : Fin 22 => g.val⁻¹ y) hx
  simpa only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    Equiv.Perm.mul_apply, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using hy

private theorem conjugate_of_mem_standard (s : m22DesignAut)
    (hs : orderOf s = 2) (hfree : ∀ x : Fin 22, s.val x ≠ x)
    (hmem : s ∈ standardSylow) :
    ∃ g : m22DesignAut, g * representative * g⁻¹ = s := by
  obtain ⟨i, hi⟩ := rowSylow_surjective ⟨s, hmem⟩
  have he : rowElement i = s := congrArg Subtype.val hi
  subst s
  rcases FixedPointFree.row_cases i with hsquare | hfix | hconj
  · obtain ⟨x, hx⟩ := hsquare
    have hp : rowElement i ^ 2 = 1 := hs ▸ pow_orderOf_eq_one (rowElement i)
    have hf := congrArg (fun g : m22DesignAut => g.val x) hp
    change (rowElement i).val ((rowElement i).val x) = x at hf
    simp only [rowElement_apply] at hf
    exact (hx hf).elim
  · obtain ⟨x, hx⟩ := hfix
    exact (hfree x ((rowElement_apply i x).trans hx)).elim
  · let u : M22 := innerWord (conjugatingWord (conjugatingIndex i))
    let g : m22DesignAut := ⟨u.val, M22_le_m22DesignAut u.property⟩
    refine ⟨g, ?_⟩
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change u.val (representative.val x) = (rowElement i).val (u.val x)
    simp only [representative_apply, rowElement_apply, u, innerWord_apply]
    exact (hconj x).symm

/-- Every fixed-point-free design involution is conjugate to the actual marked one.
No assertion about the other involution classes is needed. -/
theorem exists_representative_conjugator (s : m22DesignAut) (hs : orderOf s = 2)
    (hfree : (fixedPoints s).card = 0) :
    ∃ g : m22DesignAut, g * representative * g⁻¹ = s := by
  have hz : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hz.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22DesignAut Q standardSylow
  let e : MulAut m22DesignAut := MulAut.conj g
  have hmem : e s ∈ standardSylow := by
    rw [← hg]
    change e s ∈ (Q : Subgroup m22DesignAut).map e.toMonoidHom
    exact mem_map_of_mem e.toMonoidHom (hQ (mem_zpowers s))
  obtain ⟨k, hk⟩ := conjugate_of_mem_standard (e s) ((e.orderOf_eq s).trans hs)
    (moves_conj g s (moves_of_card_zero s hfree)) hmem
  refine ⟨g⁻¹ * k, ?_⟩
  calc
    _ = g⁻¹ * (k * representative * k⁻¹) * g := by group
    _ = s := by rw [hk]; dsimp [e, MulAut.conj_apply]; group

private theorem conjugate_mem_centralizer (g s : m22DesignAut) (x : M22)
    (hx : x ∈ centralizer s) :
    m22DesignAutToAut g x ∈ centralizer (g * s * g⁻¹) := by
  rw [centralizer, MulAut.mem_fixedSubgroup] at hx ⊢
  simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
    MulEquiv.symm_apply_apply, hx]

/-- The full fixed subgroups correspond by conjugation with the given design element. -/
noncomputable def centralizerConjEquiv (g s : m22DesignAut) :
    centralizer s ≃* centralizer (g * s * g⁻¹) where
  toFun x := ⟨m22DesignAutToAut g x.val, by
    exact conjugate_mem_centralizer g s x.val x.property⟩
  invFun x := ⟨(m22DesignAutToAut g).symm x.val, by
    have hf := conjugate_mem_centralizer g⁻¹ (g * s * g⁻¹) x.val x.property
    have he : g⁻¹ * (g * s * g⁻¹) * (g⁻¹)⁻¹ = s := by group
    rw [he] at hf
    simpa only [map_inv, MulAut.inv_apply] using hf⟩
  left_inv x := Subtype.ext ((m22DesignAutToAut g).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((m22DesignAutToAut g).apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((m22DesignAutToAut g).map_mul x.val y.val)

/-- The isomorphism retains the literal ambient permutation conjugation. -/
theorem centralizerConjEquiv_apply (g s : m22DesignAut) (x : centralizer s) :
    ((centralizerConjEquiv g s x).val : Equiv.Perm (Fin 22)) =
      g.val * (x.val : Equiv.Perm (Fin 22)) * g.val⁻¹ :=
  m22DesignAutToAut_apply_perm g x.val

/-- Conjugacy identifies each full fixed-point-free centralizer with the marked one. -/
theorem centralizer_equiv_representative (s : m22DesignAut) (hs : orderOf s = 2)
    (hfree : (fixedPoints s).card = 0) :
    Nonempty (centralizer representative ≃* centralizer s) := by
  obtain ⟨g, rfl⟩ := exists_representative_conjugator s hs hfree
  exact ⟨centralizerConjEquiv g representative⟩

end Sporadic.Mathieu.M22OuterCentralizers.FixedPointFree
