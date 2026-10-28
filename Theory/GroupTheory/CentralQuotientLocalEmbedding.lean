module
public import Theory.GroupTheory.CentralQuotientLocalMarking

/-!
# Embedding local subgroups through a central quotient

If P/O₂(P) is centerless, the kernel of P → K/Z(K) is a two-group.
Its image in K is central and therefore normal. When O₂(K) is trivial,
this kernel vanishes. Thus the original subgroup P embeds in the central
quotient, even when the full center of K is nontrivial.

Source application: Aschbacher--Smith 4.4.10--12, printed pp.621--623.
-/

public section
open Subgroup
namespace Theory.GroupTheory.CentralQuotientLocalMarking
variable {K : Type*} [Group K]

/-- A subgroup with centerless two-core quotient embeds in the ambient
central quotient when the ambient two-core is trivial. -/
theorem subgroupMap_injective_of_twoCore_eq_bot (P : Subgroup K)
    (hP : center (P ⧸ pCore 2 P) = ⊥) (hK : pCore 2 K = ⊥) :
    Function.Injective ((QuotientGroup.mk' (center K)).subgroupMap P) := by
  let f := (QuotientGroup.mk' (center K)).subgroupMap P
  let C := f.ker.map P.subtype
  have hC : C ≤ center K := by
    rintro _ ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
  have hn : C.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [mem_center_iff.mp (hC hx) g,mul_inv_cancel_right]
    exact hx
  have hp : IsPGroup 2 C :=
    (pCore_isPGroup.to_le (subgroupMap_ker_le_pCore 2 P hP)).map P.subtype
  have hCK : C ≤ pCore 2 K := le_sSup ⟨hn,hp⟩
  have hb : C = ⊥ := bot_unique (hCK.trans_eq hK)
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  exact Subtype.ext (show (x : K) = 1 from hb.le (mem_map_of_mem P.subtype hx))

end Theory.GroupTheory.CentralQuotientLocalMarking
