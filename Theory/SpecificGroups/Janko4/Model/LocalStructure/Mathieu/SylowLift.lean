module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowGeometry
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Sylow-compatible Mathieu seeds above the Janko four two-core quotient

Pull the native Mathieu local subgroup back through the actual two-core
quotient. Every automorphism preserving the prescribed Sylow preserves this
full preimage. Its two-core quotient is M₂₄, and every square in its two-core
lies in the original kernel, since the native Mathieu kernel is elementary.
No splitting or replacement of the covering group is used.

This supplies the local seed for the J₄ strict-enlargement escape in
Aschbacher--Smith, 12.5.11(2), printed p.821. The native ATLAS subgroup and
matrix certificates retain their attribution through the imported modules.
-/

public noncomputable section
open Subgroup
namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.max1Subgroup Cardinality.localKernel

/-- The Sylow-compatible Mathieu seed lifts through the whole two-core kernel. -/
theorem exists_sylow_mathieu_seed_of_two_core
    {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* Model) (P : Sylow 2 X) :
    ∃ B : Subgroup X, (P : Subgroup X) ≤ B ∧
      (∀ a : MulAut X, (P : Subgroup X).map a.toMonoidHom = P →
        B.map a.toMonoidHom = B) ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M24) ∧
      (∀ x : B, x ∈ pCore 2 B → (x : X) ^ 2 ∈ pCore 2 X) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 X := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨R,hPR,⟨er⟩,hinv,_⟩ := exists_sylow_mathieu_seed (P.mapSurjective hq)
  let B := R.comap q
  let f := q.subgroupComap R
  have hf : Function.Surjective f := by
    intro r
    obtain ⟨x,hx⟩ := hq r
    exact ⟨⟨x,show q x ∈ R from hx ▸ r.property⟩,Subtype.ext hx⟩
  have hfk : IsPGroup 2 f.ker := by
    have he : f.ker = q.ker.subgroupOf B := by
      ext x
      exact Subtype.ext_iff
    rw [he,hk]
    exact pCore_isPGroup.comap_subtype
  let em : (R ⧸ pCore 2 R) ≃* Sporadic.Mathieu.M24 :=
    (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (localKernel_eq_twoCore matrixA_mul_self matrixB_pow_four).symm).trans
        (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four))
  refine ⟨B,?_,?_,⟨(f.pCoreQuotientEquiv hf hfk).trans em⟩,?_⟩
  · intro x hx
    exact hPR (mem_map_of_mem q hx)
  · intro a ha
    let aq := MulAut.congr e ((pCore 2 X).quotientAut a)
    have he (x : X) : aq (q x) = q (a x) := by
      simp only [aq,q,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
        MulAut.congr_apply,MulEquiv.trans_apply,e.symm_apply_apply,quotientAut_apply_mk]
    have heh : aq.toMonoidHom.comp q = q.comp a.toMonoidHom := MonoidHom.ext he
    have hPq : ((P.mapSurjective hq : Sylow 2 Model) : Subgroup Model).map aq.toMonoidHom =
        (P.mapSurjective hq : Subgroup Model) := by
      change ((P : Subgroup X).map q).map aq.toMonoidHom = (P : Subgroup X).map q
      rw [map_map,heh,←map_map,ha]
    have hR := hinv aq hPq
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      change q (a x) ∈ R
      rw [←he]
      exact hR ▸ mem_map_of_mem aq.toMonoidHom hx
    · rw [card_map_of_injective a.injective]
  · intro x hx
    have hfr : f x ∈ pCore 2 R := by
      change x ∈ (pCore 2 R).comap f
      rw [f.comap_pCore_of_ker_isPGroup hf hfk]
      exact hx
    have hem : er (f x) ∈ Cardinality.localKernel matrixA_mul_self matrixB_pow_four := by
      rw [localKernel_eq_twoCore]
      exact (pCore_map_iso 2 er) ▸ mem_map_of_mem er.toMonoidHom hfr
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    have hs : er (f x) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ hem
    have hf2 : f x ^ 2 = 1 := er.injective (by simpa only [map_pow,map_one] using hs)
    have hq2 : q ((x : X) ^ 2) = 1 := by
      rw [map_pow]
      exact congrArg R.subtype hf2
    exact hk ▸ hq2
end Janko4.LocalStructure
