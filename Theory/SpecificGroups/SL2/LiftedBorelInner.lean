module
public import Theory.SpecificGroups.SL2.NormalBorelCore
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Inner quotient actions detected by a lifted binary rank-one Borel

For a finite group with binary PSL₂ two-core quotient, the two-residual
of a Sylow normalizer maps onto the full quotient Borel. An automorphism
preserving this Sylow and fixing the residual modulo its own two-core
therefore fixes the Borel quotient. Semilinear coverage then forces its
literal action on the original two-core quotient to be inner.

The proof retains the whole two-core kernel and transports its image;
no splitting or pointwise fixation of the lifted Borel is required.
Source application: Aschbacher–Smith 14.7.41, printed p.1061,
refs/quasithin.pdf, the outside-component binary L₂ row.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup
open EvenBorelResidual
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

/-- Fixing the lifted residual modulo its own two-core kills the field action. -/
theorem quotient_inner_of_borelResidual_fixed {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 1 < n) (e : (H ⧸ pCore 2 H) ≃* PSL(2,F))
    (P : Sylow 2 H) (α : MulAut H)
    (hP : (P : Subgroup H).map α.toMonoidHom = P)
    (hfix : ∀ b ∈ (pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype,
      b⁻¹ * α b ∈ ((pResidual 2 (normalizer (P : Set H))).map
        (normalizer (P : Set H)).subtype).pCoreIn 2) :
    (pCore 2 H).quotientAut α ∈ MulAut.innerSubgroup (H ⧸ pCore 2 H) := by
  let f : H →* PSL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let Q := P.mapSurjective hf
  let β := MulAut.congr e ((pCore 2 H).quotientAut α)
  have heq (x : H) : β (f x) = f (α x) := by
    change e ((pCore 2 H).quotientAut α (e.symm (e (QuotientGroup.mk' _ x)))) = _
    rw [e.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hQ : (Q : Subgroup PSL(2,F)).map β.toMonoidHom = Q := by
    have he : β.toMonoidHom.comp f = f.comp α.toMonoidHom := MonoidHom.ext heq
    change ((P : Subgroup H).map f).map β.toMonoidHom = (P : Subgroup H).map f
    rw [Subgroup.map_map,he,←Subgroup.map_map,hP]
  let B := (pResidual 2 (normalizer (P : Set H))).map (normalizer (P : Set H)).subtype
  have hBN : B.map f = normalizer (Q : Set PSL(2,F)) := by
    have hp : pResidual 2 (normalizer (Q : Set PSL(2,F))) = ⊤ := by
      apply (pResidual_eq_top_iff 2 _).mpr
      apply (borel_isPPerfect F ?_).of_surjective
        (sylowNormalizerEquiv F Q).symm.toMonoidHom (sylowNormalizerEquiv F Q).symm.surjective
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    change ((pResidual 2 (normalizer (P : Set H))).map _).map f = _
    rw [map_embedded_pResidual,P.normalizer_map_surjective f hf]
    change (pResidual 2 (normalizer (Q : Set PSL(2,F)))).map _ = _
    rw [hp]
    exact (MonoidHom.range_eq_map _).symm.trans (range_subtype _)
  have hBQ : (B.pCoreIn 2).map f ≤ (Q : Subgroup PSL(2,F)) := by
    rw [map_pCoreIn_of_ker_isPGroup f hk,hBN]
    have hh := pCoreIn_le_sylow (normalizer (Q : Set PSL(2,F)))
      (Q.subtype (Q : Subgroup PSL(2,F)).le_normalizer)
    rw [Sylow.coe_subtype] at hh
    exact hh.trans_eq (map_subgroupOf_eq_of_le (Q : Subgroup PSL(2,F)).le_normalizer)
  have hb := Semilinear.inner_of_sylow_borel_quotient_fixed hF Q β hQ (by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := hBN.ge hx
    rw [heq,←map_inv,←map_mul]
    exact hBQ (mem_map_of_mem f (hfix b hb)))
  obtain ⟨g,hg⟩ := (MulAut.congr_inner_iff e _).mp hb
  exact ⟨g,hg.symm⟩
end Matrix.ProjectiveSpecialLinearGroup
