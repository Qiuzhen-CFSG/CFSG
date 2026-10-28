module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalTerminal.OppositeBorels
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.TerminalOvercomponent.Centralizer
/-!
# Centralization by the terminal containing component

The opposite original block centralizes the axis Borel, and is nonsolvable.
The Borel centralizer is normal in its normalizer. Hence an actual C-component
containing this opposite block lies in that centralizer. This discharges
centralization in the terminal configuration once containment and the
linear-three recognition have been constructed.

The moving-Hall assembly owner retains that overcomponent construction,
natural marking and original Hall placement. Source: Aschbacher–Smith
10.2.3(4), printed p.747, using A.3.3(1).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02 ChapterB ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type} [Field F] [Finite F] [CharP F 2]

/-- Opposite-block containment supplies terminal centralization at the literal original Borel. -/
theorem Context.terminal_of_containing_opposite
    {H : Subgroup G} {B : Subgroup H} (ctx : Context D H B)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) (mark : NaturalMarking D e)
    (hBB : B.map H.subtype ≤ sourceOrbitBorel T L)
    (A K : Subgroup G) (hAL : A ≤ L) (hAB : A ≤ B.map H.subtype)
    (hA : Nat.card A = 2 ^ n - 1)
    (hK : K ∈ Chapter1.cComponentsIn
      (normalizer ((⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) : Set G)))
    (hmodel : Chapter1.Section02.LocalModels.IsSL K 3 (2 ^ n) ∨ ClassicalGroup.IsPSL K 3 (2 ^ n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hLK : L.map (MulAut.conj t).toMonoidHom ≤ K) :
    Nonempty (TerminalConfiguration T L (B.map H.subtype) n) := by
  obtain ⟨E,J,hE,hJ,heq,hUJ,hBJ,hlocal,hv,hfixed,hgen,hcover,hcard,hcyclic,
    hBN,hBNt,hbL,_⟩ := ctx.component_with_both_block_geometry D n hn hF e mark hBB
  have hne : A ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hA
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ n by omega)
    norm_num at hp
    omega
  obtain ⟨hS,_,_,_⟩ := ctx.original_block_axis_borel D n hn hF e mark hBB hbL A hAL hAB hne
  have hBL : (⁅baumann (T : Subgroup G),A⁆ ⊔ A : Subgroup G) ≤ L :=
    sup_le (by rw [hS]; exact inf_le_right) hAL
  have hcomm := source_original_block_commutes_prescribed_conjugate D hbL ht htn
  have hnon : ¬ Group.IsSolvable (L.map (MulAut.conj t).toMonoidHom) := by
    intro hs
    let := hs
    let f : L ≃* L.map (MulAut.conj t).toMonoidHom := (MulAut.conj t).subgroupMap L
    exact Chapter1.mem_L_not_isSolvable D.maximal.1
      (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
  have hc := source_borel_component_centralizes _ _ K hK hLK hnon
    ((le_centralizer_iff.mp hcomm).trans (centralizer_le hBL))
  exact ctx.terminal_of_overcomponent D n hn hF e mark hBB A K hAL hAB hA hK hmodel hc
end CFSG.Quasithin.Chapter10.MovingHall
