module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Sections
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Full G.6.4 from a natural binary linear normal closure

The faithful ambient representation embeds G into the full binary linear
group. The marked natural action of its normal closure already surjects onto
that linear group, so the original normal closure is all of G. Its natural
model supplies every G.6.4 clause, including the two-central conclusion.

Source: Aschbacher–Smith G.6.4(1)–(4), printed pp.345–346.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {κ : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.conclusion_of_binary_linear_normalClosure
    (h : Hypotheses κ ρ a q) {n : ℕ} (hn : 2 ≤ n) (hn5 : n ≤ 5)
    (e : ActionEquiv (ρ.comp (normalClosure ({a} : Set G)).subtype)
      (linearNatural BinaryField.two n)) : Conclusion ρ a := by
  let K := normalClosure ({a} : Set G)
  let E := e.linearEquiv
  let j₀ : G →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hj₀ : Function.Injective j₀ := by
    intro x y he
    apply h.faithful
    exact congrArg LinearEquiv.toLinearMap he
  let j : G →* BinaryLinear.GL (Fin n → ZMod 2) :=
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr E).toMonoidHom.comp j₀
  have hj : Function.Injective j :=
    (BinaryLinear.SmallParabolicLevi.linearGroupCongr E).injective.comp hj₀
  have hjK (k : K) : j k = BinaryLinear.OuterCyclic.slEquivLinear n (e.groupEquiv k) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    change E (ρ k (E.symm (E v))) = _
    rw [E.symm_apply_apply]
    exact e.intertwines k v
  have hKtop : K = ⊤ := by
    apply top_unique
    intro g _
    let k : K := e.groupEquiv.symm ((BinaryLinear.OuterCyclic.slEquivLinear n).symm (j g))
    have he : j k = j g := by
      rw [hjK]
      exact (congrArg (BinaryLinear.OuterCyclic.slEquivLinear n)
        (e.groupEquiv.apply_symm_apply _)).trans
          ((BinaryLinear.OuterCyclic.slEquivLinear n).apply_symm_apply _)
    exact hj he ▸ k.property
  have hmodel : HasModelOn ρ ⊤ ⊤ (binaryLinearAction n) := by
    refine ⟨(MulEquiv.subgroupCongr hKtop.symm).trans
      (e.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear n)),
      Submodule.topEquiv.trans E, ?_, ?_⟩
    · intro _ _
      exact Submodule.mem_top
    · intro k v
      exact e.intertwines (MulEquiv.subgroupCongr hKtop.symm k) v
  have hmoved : subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
    have hm := lemma_G_6_2_1 ρ a h.generated
    rwa [show normalClosure ({a} : Set G) = ⊤ from hKtop] at hm
  refine ⟨Or.inl ⟨hKtop, ?_, hmoved⟩, ?_⟩
  · rw [hmoved]
    exact Or.inl ⟨n,hn,hn5,hmodel⟩
  · intro _ _
    exact ⟨hKtop,Or.inl ⟨n,hn,hn5,hmodel⟩⟩
end CFSG.Quasithin.ChapterG.Section06
