module

public import Theory.SpecificGroups.GL2.ThreeQuaternionUniqueness

/-!
# Quaternion normality in a faithful ternary representation

If H/F embeds in GL₂(3), every subgroup Q containing F with Q/F ≅ Q₈
is normal in H. Its faithful image is the unique quaternion subgroup of
GL₂(3); pulling normality back twice gives the assertion. Surjectivity of
the representation is unnecessary.

This strengthens the quotient form used in Aschbacher–Smith, combined
manuscript of 1 March 2004, proof of 16.4.9(2), printed p.1191.
-/

public section

namespace Matrix.GeneralLinearGroup
open Subgroup
variable {H : Type*} [Group H]

/-- Quaternion normality only requires a faithful representation of the
relative quotient, rather than an identification with the full matrix group. -/
theorem normal_of_three_faithful_quotient (F Q : Subgroup H) [F.Normal] (hFQ : F ≤ Q)
    (ρ : H ⧸ F →* GL (Fin 2) (ZMod 3)) (hρ : Function.Injective ρ)
    (hQ : Nonempty ((Q ⧸ F.subgroupOf Q) ≃* QuaternionGroup 2)) : Q.Normal := by
  obtain ⟨eQ⟩ := hQ
  let q := QuotientGroup.mk' F
  let f := q.comp Q.subtype
  have hk : f.ker = F.subgroupOf Q := by
    ext x
    simp [f, q, mem_subgroupOf]
  let a : (Q ⧸ F.subgroupOf Q) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hr : f.range = Q.map q := by rw [MonoidHom.range_comp, range_subtype]
  let b : Q.map q ≃* QuaternionGroup 2 :=
    ((MulEquiv.subgroupCongr hr).symm.trans a.symm).trans eQ
  let P := (Q.map q).map ρ
  let c : P ≃* QuaternionGroup 2 :=
    ((Q.map q).equivMapOfInjective ρ hρ).symm.trans b
  let _ : P.Normal := three_quaternion_subgroup_normal P ⟨c⟩
  exact normal_of_faithful_quotient_image F Q hFQ ρ hρ P rfl

end Matrix.GeneralLinearGroup
