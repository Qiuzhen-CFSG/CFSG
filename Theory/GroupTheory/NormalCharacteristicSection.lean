module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Normal lifts of characteristic sections

If `Z` and `H` are normal in a group, conjugation preserves the section
`H/(Z ∩ H)`. A characteristic subgroup of this section therefore lifts to
a normal subgroup of the original group. The proof descends the actual
conjugation automorphism; it does not require `Z` to be characteristic in `H`.

This is the relative-normality step in Aschbacher--Smith, Lemma 14.2.21.
-/

/-- Lift a characteristic subgroup through a section with ambient-normal kernel. -/
public theorem Subgroup.normal_preimage_characteristic_quotient
    {D F : Type*} [Group D] [Group F]
    (Z QH QK : Subgroup D) [Z.Normal] [QH.Normal]
    (e : QH ⧸ Z.subgroupOf QH ≃* F)
    (B : Subgroup F) [B.Characteristic]
    (hQK : QK = (B.comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf QH)))).map QH.subtype) :
    QK.Normal := by
  let N := Z.subgroupOf QH
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  refine ⟨?_⟩
  intro x hx g
  rw [hQK] at hx ⊢
  obtain ⟨q, hq, rfl⟩ := hx
  let a : MulAut QH := MulAut.conjNormal g
  have hNa : N.map a.toMonoidHom = N := by
    ext y
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Subgroup.Normal.conj_mem (inferInstance : Z.Normal) (n : D) hn g
    · intro hy
      refine ⟨a.symm y, ?_, a.apply_symm_apply y⟩
      change ((a.symm y : QH) : D) ∈ Z
      rw [MulAut.conjNormal_symm_apply]
      simpa only [inv_inv] using
        Subgroup.Normal.conj_mem (inferInstance : Z.Normal) (y : D) hy g⁻¹
  let b := QuotientGroup.congr N N a hNa
  let c : MulAut F := (e.symm.trans b).trans e
  have hbc : c (f q) ∈ B :=
    Subgroup.characteristic_iff_le_comap.mp inferInstance c hq
  refine ⟨a q, ?_, rfl⟩
  change f (a q) ∈ B
  have he : c (f q) = f (a q) := by
    simp only [c, f, MulEquiv.trans_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact congrArg e (QuotientGroup.congr_mk N N a hNa q)
  exact he ▸ hbc
