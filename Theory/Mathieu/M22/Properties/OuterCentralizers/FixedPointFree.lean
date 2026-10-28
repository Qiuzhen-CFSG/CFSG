module

public import Theory.Mathieu.M22.Properties.OuterCentralizers.FixedPointFree.Conjugacy
public import Theory.Mathieu.M22.Properties.OuterCentralizers.FixedPointFree.QuotientModel
public import Mathlib.GroupTheory.GroupExtension.Defs
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# The fixed-point-free outer M₂₂ centralizer: assembly

All fixed-point-free design involutions are conjugate to the explicit
representative. Transport its actual elementary-kernel extension along
this conjugation, and identify the five-point quotient with the genuine
Suzuki matrix carrier. The extension and matrix comparison remain explicit
inputs here until their separate concrete calculations are supplied.

This is conditional assembly for Aschbacher–Smith 16.1.5(5), printed p.1171;
it does not yet assert the unconditional source theorem. No splitting is
assumed, and neither quotient is inferred merely from its order.
-/

public section
namespace Sporadic.Mathieu.M22OuterCentralizers
open FixedPointFree

private noncomputable def transportExtension
    {N E F Q R : Type*} [Group N] [Group E] [Group F] [Group Q] [Group R]
    (S : GroupExtension N E Q) (e : E ≃* F) (q : Q ≃* R) :
    GroupExtension N F R where
  inl := e.toMonoidHom.comp S.inl
  rightHom := q.toMonoidHom.comp (S.rightHom.comp e.symm.toMonoidHom)
  inl_injective := e.injective.comp S.inl_injective
  rightHom_surjective := q.surjective.comp (S.rightHom_surjective.comp e.symm.surjective)
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      change q (S.rightHom (e.symm (e (S.inl n)))) = 1
      rw [e.symm_apply_apply, S.rightHom_inl, map_one]
    · intro hx
      have hk : e.symm x ∈ S.rightHom.ker := by
        change q (S.rightHom (e.symm x)) = 1 at hx
        exact (map_eq_one_iff q q.injective).mp hx
      rw [← S.range_inl_eq_ker_rightHom] at hk
      obtain ⟨n, hn⟩ := hk
      refine ⟨n, ?_⟩
      change e (S.inl n) = x
      rw [hn, e.apply_symm_apply]

/-- The genuine representative extension suffices for every fixed-point-free
involution, via the proved design conjugacy and full centralizer transport. -/
theorem fixedPointFree_extension_of_representative
    (hrep : Nonempty (GroupExtension (Fin 4 → Multiplicative (ZMod 2))
      (centralizer representative) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)))
    (s : m22DesignAut) (hs : orderOf s = 2) (hfree : (fixedPoints s).card = 0) :
    Nonempty (GroupExtension (Fin 4 → Multiplicative (ZMod 2)) (centralizer s)
      (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) := by
  obtain ⟨S⟩ := hrep
  obtain ⟨e⟩ := centralizer_equiv_representative s hs hfree
  exact ⟨transportExtension S e (MulEquiv.refl _)⟩

/-- Assembly from the literal representative extension and an actual
multiplicative equivalence of its five-point quotient with `Sz(2)`. -/
theorem fixedPointFree_extension_of_models
    (hrep : Nonempty (GroupExtension (Fin 4 → Multiplicative (ZMod 2))
      (centralizer representative) fiveNormalizer))
    (hmodel : Nonempty (fiveNormalizer ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (s : m22DesignAut) (hs : orderOf s = 2) (hfree : (fixedPoints s).card = 0) :
    Nonempty (GroupExtension (Fin 4 → Multiplicative (ZMod 2)) (centralizer s)
      (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)) := by
  obtain ⟨S⟩ := hrep
  obtain ⟨q⟩ := hmodel
  obtain ⟨e⟩ := centralizer_equiv_representative s hs hfree
  exact ⟨transportExtension S e q⟩

end Sporadic.Mathieu.M22OuterCentralizers
