module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases.Placement

/-!
# The actual marked automorphism in the simple-component sieve

Restrict conjugation by the marked involution to the normal component and
transport it through the supplied model isomorphism. Binary irreducibility
ensures this automorphism is nontrivial. The ambient central Sylow condition
gives an intrinsic Sylow subgroup which it fixes pointwise. A fixed cubic in
the model therefore contradicts the source centralizer hypothesis.

Source: Aschbacher--Smith, 15.3.58, printed p.1149.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- The marked involution induces a genuine involutory model automorphism,
fixing an intrinsic Sylow subgroup. Its fixed elements are exactly the model
elements whose actual images commute with the marked involution. -/
theorem SourceData.marked_automorphism_data {D : Type*} [Group D]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) (e : K ≃* D) :
    letI : K.Normal := hK.normal
    let a := MulAut.congr e (MulAut.conjNormal (H := K) v)
    orderOf a = 2 ∧
      (∃ S : Sylow 2 D, ∀ x ∈ S, a x = x) ∧
      (∀ d : D, a d = d ↔ Commute v (e.symm d : H)) := by
  let : K.Normal := hK.normal
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  let a := MulAut.congr e (MulAut.conjNormal (H := K) v)
  have hv : v ^ 2 = 1 := h.involution ▸ pow_orderOf_eq_one v
  have ha : a ^ 2 = 1 := by
    dsimp only [a]
    rw [← map_pow, ← map_pow, hv, map_one, map_one]
  have hane : a ≠ 1 := by
    intro he
    have hc : v ∈ centralizer (K : Set H) := by
      rw [← MulAut.conjNormal_ker_eq_centralizer]
      change MulAut.conjNormal (H := K) v = 1
      apply (MulAut.congr e).injective
      exact he.trans (map_one _).symm
    have hv1 := BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      ρ K h.faithful hv hc
    have ho := h.involution
    rw [hv1, orderOf_one] at ho
    omega
  refine ⟨orderOf_eq_prime ha hane, ?_, ?_⟩
  · obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
    let R : Sylow 2 D := S.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨R, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    change e (MulAut.conjNormal (H := K) v (e.symm (e y))) = e y
    rw [e.symm_apply_apply]
    apply congrArg e
    apply Subtype.ext
    change v * (y : H) * v⁻¹ = y
    have hyT : (y : H) ∈ T := by
      rw [hS] at hy
      exact hy
    obtain ⟨z, hz, he⟩ := h.marked_central
    change (z : H) = v at he
    have hzcomm := congrArg (fun t : (T : Subgroup H) => (t : H))
      ((mem_center_iff.mp hz) ⟨y, hyT⟩)
    change (y : H) * (z : H) = (z : H) * y at hzcomm
    rw [he] at hzcomm
    rw [← hzcomm, mul_inv_cancel_right]
  · intro d
    constructor
    · intro hd
      have he := congrArg (fun x : D => (e.symm x : H)) hd
      change (e.symm (e (MulAut.conjNormal (H := K) v (e.symm d))) : H) = _ at he
      rw [e.symm_apply_apply] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hc
      apply e.symm.injective
      change e.symm (e (MulAut.conjNormal (H := K) v (e.symm d))) = e.symm d
      rw [e.symm_apply_apply]
      apply Subtype.ext
      change v * (e.symm d : H) * v⁻¹ = (e.symm d : H)
      exact mul_inv_eq_iff_eq_mul.mpr hc.eq

/-- A model-independent existential version of the marked automorphism data. -/
theorem SourceData.marked_automorphism {D : Type*} [Group D]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) (e : K ≃* D) :
    ∃ a : MulAut D, orderOf a = 2 ∧
      (∃ S : Sylow 2 D, ∀ x ∈ S, a x = x) ∧
      (∀ d : D, a d = d ↔ Commute v (e.symm d : H)) := by
  let : K.Normal := hK.normal
  exact ⟨_, h.marked_automorphism_data hK e⟩

/-- A fixed order-three model element violates the actual source centralizer
condition after transport through the component inclusion. -/
theorem SourceData.no_model_cubic_commuting {D : Type*} [Group D]
    (h : SourceData ρ X T v s) (e : K ≃* D) (d : D)
    (hd : orderOf d = 3) (hc : Commute v (e.symm d : H)) : False := by
  apply h.no_cubic_centralizer (e.symm d : H)
  · rw [Subgroup.orderOf_coe, e.symm.orderOf_eq]
    exact hd
  · rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    exact hc.symm.eq

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
