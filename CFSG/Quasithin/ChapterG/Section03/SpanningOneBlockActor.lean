module

public import CFSG.Quasithin.ChapterG.Section03.SpanningBlockModels
import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# The whole actor of a unique spanning G.3 block

The unique block spans the original space. Its full restriction action
therefore contains every original linear automorphism. Consequently both
the root-generated group and the supplied actor are the whole linear group,
with no replacement of the module or its action.

Source application: Aschbacher--Smith12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- A unique spanning full block is the whole original linear space and actor. -/
theorem spanning_one_block_actor
    {Q : Subgroup (BinaryLinear.GL V)} {Δ : Set V}
    (hf : FullAction Q Δ) (hd : Decomposition Q Δ)
    (hspan : Submodule.span (ZMod 2) Δ = ⊤)
    (hone : Nat.card (OrbitBlock Q Δ) = 1) :
    (∀i : OrbitBlock Q Δ, blockSpace Q Δ i = ⊤) ∧
      generated Q Δ = ⊤ ∧ Q = ⊤ := by
  obtain ⟨i,hi⟩ := Nat.card_eq_one_iff_exists.mp hone
  have hspace (j : OrbitBlock Q Δ) : blockSpace Q Δ j = ⊤ := by
    rw [hi j]
    have hs : (⨆j : OrbitBlock Q Δ,blockSpace Q Δ j) = blockSpace Q Δ i := by
      apply le_antisymm
      · exact iSup_le fun j => (hi j) ▸ le_rfl
      · exact le_iSup _ i
    exact hs.symm.trans (hd.space_span.trans hspan)
  let S := blockSpace Q Δ i
  let e : S ≃ₗ[ZMod 2] V :=
    (LinearEquiv.ofEq S ⊤ (hspace i)).trans Submodule.topEquiv
  have he (v : S) : e v = (v : V) := rfl
  have hblock : blockGroup Q Δ i = ⊤ := by
    apply top_unique
    intro g _
    let gs := (SmallParabolicLevi.linearGroupCongr e).symm g
    obtain ⟨k,hk⟩ := hf.surjective i gs
    have hkg : k.val = g := by
      apply LinearEquiv.ext
      intro v
      obtain ⟨w,rfl⟩ := e.surjective v
      have hh := congrArg (fun f : BinaryLinear.GL S => e (f w)) hk
      change k.val (e w) = e (e.symm (g (e w))) at hh
      simpa only [e.apply_symm_apply] using hh
    exact hkg ▸ k.property
  have hgen : generated Q Δ = ⊤ := by
    apply top_unique
    rw [←hd.group_join]
    exact hblock ▸ le_iSup (blockGroup Q Δ) i
  exact ⟨hspace,hgen,top_unique (hgen ▸ generated_le Q Δ)⟩

end CFSG.Quasithin.ChapterG.Section03
