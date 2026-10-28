module

public import CFSG.Quasithin.ChapterG.Section03.LocalRank.Core

/-!
# Restriction to the literal total root span

The whole actor preserves the total root span. Restriction has its actual
pointwise kernel; it need not be faithful on the whole actor. On the
root-generated subgroup, all displacements lie in that span, so a restriction
kernel element lies in its binary radical and hence in the ambient two-core.
Thus restriction is faithful on the generated subgroup when that core is trivial.

Source application: Aschbacher--Smith12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The exact action and kernel on the total root span, with faithfulness
on the original generated subgroup under the trivial-two-core guard. -/
theorem root_span_action
    {Q : Subgroup (BinaryLinear.GL V)} [Finite Q] {Δ : Set V}
    (h : Hypotheses Q Δ) (hcore : pCore 2 Q = ⊥) :
    ∃ hpar : Q ≤ parabolic (Submodule.span (ZMod 2) Δ),
      let ρ := action Q (Submodule.span (ZMod 2) Δ) hpar
      (∀g : Q,∀v : Submodule.span (ZMod 2) Δ,(ρ g v : V)=g.val v) ∧
      ρ.ker=fixingKernel Q (Submodule.span (ZMod 2) Δ) ∧
      Function.Injective (ρ.comp (Subgroup.inclusion (generated_le Q Δ))) := by
  let S := Submodule.span (ZMod 2) Δ
  have hs (g : Q) (v : V) (hv : v∈S) : g.val v∈S := by
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span (h.stable g.val g.property v hv)
    | zero => simpa only [map_zero] using S.zero_mem
    | add v w _ _ hv hw => simpa only [map_add] using S.add_mem hv hw
    | smul c v _ hv => simpa only [map_smul] using S.smul_mem c hv
  have hp : Q≤parabolic S := by
    intro g hg v
    refine ⟨?_,hs ⟨g,hg⟩ v⟩
    intro hv
    have hh := hs (⟨g,hg⟩ : Q)⁻¹ (g v) hv
    change g.symm (g v)∈S at hh
    simpa only [g.symm_apply_apply] using hh
  refine ⟨hp,fun _ _ => rfl,action_ker_eq _ _ _,?_⟩
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hfix (v : V) (hv : v∈S) : g.val v=v :=
    congrArg (fun F : BinaryLinear.GL S => (F ⟨v,hv⟩ : V)) hg
  have hr : (⟨g.val,generated_le Q Δ g.property⟩ : Q)∈pCore 2 Q :=
    LocalRank.total_radical_le_pCore h ⟨hfix,generated_le_quotientFixer Q Δ g.property⟩
  rw [hcore,mem_bot] at hr
  exact Subtype.ext (congrArg (fun q : Q => q.val) hr)

end CFSG.Quasithin.ChapterG.Section03
