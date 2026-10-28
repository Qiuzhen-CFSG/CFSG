module
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Seven-letter actions of characteristic A₇ quotients

Conjugation on a characteristic quotient A/N ≃ A₇ extends its marked
projection to the normalizer, using Aut(A₇) = S₇. A solvable N and a
solvable quotient by A give a solvable action kernel. The H-star application
uses N = O₂,Z(A), retaining the possible odd central cover of A₇.

Source: Aschbacher–Smith, 12.2.7, printed pp.797–798.
-/

public noncomputable section
open Subgroup
namespace alternatingGroup.SevenComponent
variable {G : Type*} [Group G]

/-- Extend the literal projection on a normal subgroup's characteristic quotient. -/
theorem exists_characteristic_extension (A : Subgroup G) [A.Normal]
    (N : Subgroup A) [N.Characteristic] (e : (A ⧸ N) ≃* alternatingGroup (Fin 7)) :
    ∃ f : G →* Equiv.Perm (Fin 7),
      ∀ a : A, f a = (e (QuotientGroup.mk' N a)).val := by
  let c : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let b := (MulAut.congr e).toMonoidHom.comp (normalQuotientAction A N)
  let f := c.symm.toMonoidHom.comp b
  refine ⟨f,fun a => ?_⟩
  apply c.injective
  change c (c.symm (b a)) = _
  rw [c.apply_symm_apply]
  change MulAut.congr e (normalQuotientAction A N a) =
    MulAut.conjNormal (e (QuotientGroup.mk' N a)).val
  rw [normalQuotientAction_inner,MulAut.conjNormal_val]
  ext x
  simp [MulAut.congr_apply,MulAut.conj_apply]

/-- The extension sends the given normal subgroup onto the alternating group. -/
theorem characteristic_extension_image (A : Subgroup G) (N : Subgroup A) [N.Normal]
    (e : (A ⧸ N) ≃* alternatingGroup (Fin 7))
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ a : A, f a = (e (QuotientGroup.mk' N a)).val) :
    A.map f = alternatingGroup (Fin 7) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    rw [hf ⟨a,ha⟩]
    exact (e (QuotientGroup.mk' N ⟨a,ha⟩)).property
  · intro hx
    obtain ⟨q,hq⟩ := e.surjective ⟨x,hx⟩
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective N q
    exact ⟨a,a.property,(hf a).trans (congrArg Subtype.val hq)⟩

/-- Solvable quotient kernels remain solvable in the actual ambient action. -/
theorem characteristic_extension_kernel_solvable (A : Subgroup G) [A.Normal]
    (N : Subgroup A) [N.Normal] [Group.IsSolvable N] [Group.IsSolvable (G ⧸ A)]
    (e : (A ⧸ N) ≃* alternatingGroup (Fin 7))
    (f : G →* Equiv.Perm (Fin 7))
    (hf : ∀ a : A, f a = (e (QuotientGroup.mk' N a)).val) :
    Group.IsSolvable f.ker := by
  let q := (QuotientGroup.mk' A).comp f.ker.subtype
  let j : q.ker →* N := {
    toFun x := ⟨⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩,by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.map_eq_one_iff.mp
      apply Subtype.ext
      exact (hf ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩).symm.trans x.val.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (f := j) (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : N => (z.val : G)) h)))
  exact Group.isSolvable_of_ker_le_range q.ker.subtype q (by simp)
end alternatingGroup.SevenComponent
