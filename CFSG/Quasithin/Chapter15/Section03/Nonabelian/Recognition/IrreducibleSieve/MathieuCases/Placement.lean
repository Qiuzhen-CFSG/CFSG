module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Reductions
public import Theory.Representation.BinaryIrreducibleCentralizer.InnerInvolution
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Placing the marked involution in a Mathieu component

Intersect the ambient Sylow subgroup with the actual normal component join.
The marked central involution fixes this intrinsic Sylow subgroup pointwise.
A model calculation making its induced automorphism inner, followed by
centerlessness and the binary Schur argument, places the involution in the join.
In particular, membership is proved before applying an inner involution rank.

Source: Aschbacher–Smith, 15.3.58, printed p.1149.
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

/-- Pointwise Sylow-fixing automorphisms of an actual component model place
the marked central involution in the component join itself. -/
theorem marked_mem_component_of_pointwise_fixers {D : Type*} [Group D] [Finite D]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) (e : K ≃* D)
    (hi : ∀ (a : MulAut D) (S : Sylow 2 D), (∀ x ∈ S, a x = x) →
      ∃ d : D, a = MulAut.conj d) :
    v ∈ K := by
  let : K.Normal := hK.normal
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  let a := MulAut.congr e (MulAut.conjNormal (H := K) v)
  let R : Sylow 2 D := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hf : ∀ x ∈ R, a x = x := by
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
  let : IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  exact BinaryIrreducibleCentralizer.inner_square_one_mem ρ K h.faithful
    hK.center_eq_bot (h.involution ▸ pow_orderOf_eq_one v)
    ((MulAut.congr_inner_iff e _).mp (hi a R hf))
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.MathieuCases
