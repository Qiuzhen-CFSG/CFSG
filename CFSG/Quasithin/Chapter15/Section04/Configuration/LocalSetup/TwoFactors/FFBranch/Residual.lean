module
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer

/-!
# Lifting the final normalization through the two-core

The actual permutation group `S₃ × S₃` has abelian derived subgroup.
Consequently the identities `Yᵢ = [Yᵢ,J]` force the images of the two factors
to commute in this quotient. The cross-commutator therefore lies in the
kernel `Q`. This makes `Y₂` normalize `Y₁Q`.

If the two-group `Q` normalizes the two-perfect group `Y₁`, then
`O²(Y₁Q) = Y₁`. Characteristicness of this residual gives normalization of
`Y₁` itself. Normality here is relative to `Y₁Q`; no two-core is substituted
for the two-residual. The quotient identification remains an explicit input
to this lifting step and must be constructed by the branch recognition proof.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, final sentence of 15.4.18, printed p.1163.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup
open scoped IsMulCommutative commutatorElement
variable {H K : Type*} [Group H] [Group K]

/-- In an abelian derived subgroup, the two commutator-generated images commute. -/
theorem factor_commutator_le_kernel (q : H →* K)
    [IsMulCommutative (_root_.commutator K)] (Y₁ Y₂ J : Subgroup H)
    (h₁ : Y₁ = ⁅Y₁, J⁆) (h₂ : Y₂ = ⁅Y₂, J⁆) : ⁅Y₂, Y₁⁆ ≤ q.ker := by
  have hi (Y : Subgroup H) (hY : Y = ⁅Y, J⁆) : Y.map q ≤ _root_.commutator K := by
    rw [hY, map_commutator, _root_.commutator_def]
    exact commutator_mono le_top le_top
  apply (Subgroup.map_eq_bot_iff _).mp
  apply le_bot_iff.mp
  rw [map_commutator]
  calc
    ⁅Y₂.map q, Y₁.map q⁆ ≤ ⁅_root_.commutator K, _root_.commutator K⁆ :=
      commutator_mono (hi Y₂ h₂) (hi Y₁ h₁)
    _ = ⊥ := commutator_self_eq_bot_iff.mpr inferInstance

/-- The quotient is identified with actual permutations, rather than a family tag. -/
theorem symmetricThreeProduct_derived_abelian :
    IsMulCommutative (_root_.commutator (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let A := alternatingGroup (Fin 3)
  let _ : IsMulCommutative A := alternatingGroup.isMulCommutative_of_card_le_three (by simp)
  have hle : _root_.commutator (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ≤ A.prod A := by
    rw [_root_.commutator_def,
      ← top_prod_top (G := Equiv.Perm (Fin 3)) (N := Equiv.Perm (Fin 3)),
      commutator_prod_prod]
    exact prod_mono alternatingGroup.commutator_perm_le alternatingGroup.commutator_perm_le
  let _ : IsMulCommutative (A.prod A) :=
    { is_comm := ⟨fun x y => Subtype.ext (Prod.ext
        (setLike_mul_comm x.property.1 y.property.1)
        (setLike_mul_comm x.property.2 y.property.2))⟩ }
  exact { is_comm := ⟨fun x y => Subtype.ext (setLike_mul_comm (hle x.property) (hle y.property))⟩ }

/-- If the commutators disappear modulo Q, normalization lifts to Y₁Q. -/
theorem normalizes_join_of_commutator_le (Q Y₁ Y₂ : Subgroup H) [Q.Normal]
    (hc : ⁅Y₂, Y₁⁆ ≤ Q) : Y₂ ≤ normalizer ((Y₁ ⊔ Q : Subgroup H) : Set H) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, r, hr, rfl⟩ := mem_sup_of_normal_right.mp hx
  have hcomm := hc (commutator_mem_commutator hg hy)
  have he : g * (y * r) * g⁻¹ = (⁅g, y⁆ * y) * (g * r * g⁻¹) := by group
  rw [he]
  exact mul_mem (mul_mem (mem_sup_right hcomm) (mem_sup_left hy))
    (mem_sup_right ((inferInstance : Q.Normal).conj_mem r hr g))

/-- This is precisely O²(Y₁Q)=Y₁, with relative characteristicness. -/
theorem normalizes_factor_of_commutator_le (Q Y₁ Y₂ : Subgroup H) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hY : IsPPerfect 2 Y₁)
    (hQY : Q ≤ normalizer (Y₁ : Set H)) (hc : ⁅Y₂, Y₁⁆ ≤ Q) :
    (pResidual 2 (Y₁ ⊔ Q : Subgroup H)).map (Y₁ ⊔ Q).subtype = Y₁ ∧
      Y₂ ≤ normalizer (Y₁ : Set H) := by
  have hres := embedded_pResidual_join_pGroup Y₁ Q hY hQ hQY
  refine ⟨hres, ?_⟩
  rw [← hres]
  exact (normalizes_join_of_commutator_le Q Y₁ Y₂ hc).trans
    (normalizer_le_normalizer_characteristic_image (Y₁ ⊔ Q) (pResidual 2 (Y₁ ⊔ Q : Subgroup H)))

/-- Apply the residual lifting argument after an actual quotient identification. -/
theorem normalizes_factor_of_symmetricThreeProduct_quotient
    (Q Y₁ Y₂ J : Subgroup H) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hY : IsPPerfect 2 Y₁)
    (hQY : Q ≤ normalizer (Y₁ : Set H))
    (h₁ : Y₁ = ⁅Y₁, J⁆) (h₂ : Y₂ = ⁅Y₂, J⁆)
    (e : (H ⧸ Q) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) :
    Y₂ ≤ normalizer (Y₁ : Set H) := by
  let _ := symmetricThreeProduct_derived_abelian
  let q := e.toMonoidHom.comp (QuotientGroup.mk' Q)
  have hker : q.ker = Q := by
    ext x
    change e (QuotientGroup.mk' Q x) = 1 ↔ x ∈ Q
    rw [← e.map_one, e.injective.eq_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (normalizes_factor_of_commutator_le Q Y₁ Y₂ hQ hY hQY
    (hker ▸ factor_commutator_le_kernel q Y₁ Y₂ J h₁ h₂)).2

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
