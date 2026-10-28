module

public import CFSG.Quasithin.ChapterG.Section03.RootSpanAction

/-!
# The full restriction image of a unique root block

The single block is exactly the literal total root span. Its full action
therefore fills the restriction image of the original actor. The original
module and the whole actor's possible restriction kernel are retained.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A unique full block makes the action on the total root span surjective. -/
theorem root_span_one_block_actor
    {Q : Subgroup (BinaryLinear.GL V)} [Finite Q] {Δ : Set V}
    (h : Hypotheses Q Δ) (hcore : pCore 2 Q = ⊥)
    (hf : FullAction Q Δ) (hd : Decomposition Q Δ)
    (hone : Nat.card (OrbitBlock Q Δ) = 1) :
    ∃hpar : Q≤parabolic (Submodule.span (ZMod 2) Δ),
      (action Q (Submodule.span (ZMod 2) Δ) hpar).range=⊤ ∧
      ∀i : OrbitBlock Q Δ,blockSpace Q Δ i=Submodule.span (ZMod 2) Δ := by
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hspace (j : OrbitBlock Q Δ) : blockSpace Q Δ j=Submodule.span (ZMod 2) Δ := by
    rw [hi j]
    have hs : (⨆j : OrbitBlock Q Δ,blockSpace Q Δ j)=blockSpace Q Δ i := by
      apply le_antisymm
      · exact iSup_le fun j => (hi j) ▸ le_rfl
      · exact le_iSup _ i
    exact hs.symm.trans hd.space_span
  obtain ⟨hp,_,_,_⟩ := root_span_action h hcore
  let S := Submodule.span (ZMod 2) Δ
  let e : blockSpace Q Δ i ≃ₗ[ZMod 2] S := LinearEquiv.ofEq _ _ (hspace i)
  refine ⟨hp,?_,hspace⟩
  apply MonoidHom.range_eq_top.mpr
  intro g
  let gs : BinaryLinear.GL (blockSpace Q Δ i) := e.trans (g.trans e.symm)
  obtain ⟨k,hk⟩ := hf.surjective i gs
  refine ⟨⟨k.val,generated_le Q i.val k.property⟩,?_⟩
  apply LinearEquiv.ext
  intro v
  obtain ⟨w,rfl⟩ := e.surjective v
  apply Subtype.ext
  have hh := congrArg (fun f : BinaryLinear.GL (blockSpace Q Δ i) => (f w : V)) hk
  exact hh

end CFSG.Quasithin.ChapterG.Section03
