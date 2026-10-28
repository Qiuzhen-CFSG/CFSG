module
public import Theory.GroupTheory.PCoreImageRestriction

/-!
# Local action kernels preserve distinct local cores

The two-core preimage formula only needs the kernel restricted to the
subgroup in question to be a two-group. Applying it to two subgroups
whose cores lie in their intersection proves that distinct cores have
distinct images. The whole ambient kernel need not be a two-group.

Source application: Aschbacher--Smith 14.3.31, printed p.1003, for the
literal quotient Ke/C_Ke(Ue).
-/

public section
open Subgroup
namespace Subgroup
variable {D E : Type*} [Group D] [Group E] [Finite D] [Finite E]

/-- The restricted kernel suffices for the intrinsic core-preimage formula. -/
theorem inf_comap_pCoreIn_eq_of_local_kernel (p : ℕ) [Fact p.Prime]
    (f : D →* E) (A : Subgroup D) (hk : IsPGroup p (f.subgroupMap A).ker) :
    A ⊓ ((A.map f).pCoreIn p).comap f = A.pCoreIn p := by
  let fA := f.subgroupMap A
  have hcore := fA.comap_pCore_of_ker_isPGroup (f.subgroupMap_surjective A) hk
  ext a
  constructor
  · rintro ⟨ha,b,hb,he⟩
    refine ⟨⟨a,ha⟩,?_,rfl⟩
    rw [←hcore]
    change fA ⟨a,ha⟩ ∈ pCore p (A.map f)
    exact (show b = fA ⟨a,ha⟩ from Subtype.ext he) ▸ hb
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a.property,fA a,hcore.ge ha,rfl⟩

/-- Distinct cores inside the overlap remain distinct after the action map. -/
theorem pCoreIn_image_ne_of_local_kernels (p : ℕ) [Fact p.Prime]
    (f : D →* E) (A B : Subgroup D)
    (hA : IsPGroup p (f.subgroupMap A).ker)
    (hB : IsPGroup p (f.subgroupMap B).ker)
    (hAB : A.pCoreIn p ≤ B) (hBA : B.pCoreIn p ≤ A)
    (hne : A.pCoreIn p ≠ B.pCoreIn p) :
    (A.map f).pCoreIn p ≠ (B.map f).pCoreIn p := by
  intro he
  apply hne
  have ha := inf_comap_pCoreIn_eq_of_local_kernel p f A hA
  have hb := inf_comap_pCoreIn_eq_of_local_kernel p f B hB
  apply le_antisymm
  · intro x hx
    exact hb.le ⟨hAB hx,he ▸ (ha.ge hx).2⟩
  · intro x hx
    exact ha.le ⟨hBA hx,he.symm ▸ (hb.ge hx).2⟩
end Subgroup

