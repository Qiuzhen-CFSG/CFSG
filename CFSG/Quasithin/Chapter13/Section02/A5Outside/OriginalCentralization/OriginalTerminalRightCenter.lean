module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NormalizedResidualF11
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalBorel

/-!
# The original central line in a terminal right parabolic

In the terminal branch H centralizes the original line V₁. Its selected
right factor therefore centralizes that line, as do the source two-group
and the full left Borel. The line is contained in the source two-group,
so the actual right parabolic has nontrivial center.

This conclusion requires neither a prepared pair nor an amalgam comparison.
It applies to every selected subgroup of the original H.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H R : Subgroup G}

/-- The actual terminal centralizer hypothesis places the original line in
the center of every selected right parabolic, whose center is nontrivial. -/
theorem original_terminal_right_center
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G)) (hR : R ≤ H) :
    let P := ChapterF.Source.parabolic ![L,R] (Global.sourceS L H) 1
    V₁ ≤ (center P).map P.subtype ∧ center P ≠ ⊥ := by
  dsimp only
  let S := Global.sourceS L H
  let P := ChapterF.Source.parabolic ![L,R] S 1
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans f.symm⟩
  have hleft : S ⊓ L = (T : Subgroup G) ⊓ L :=
    (d.chosen.rankOne_sourceS_intersection_left h hpsl hH).1
  have hline : V₁ ≤ V := d.flag.one_le_two.trans d.flag.two_le_V
  have hVS : V₁ ≤ S := by
    have hv : V₁ ≤ (T : Subgroup G) ⊓ L :=
      le_inf (hline.trans d.chosen.le_sylow) (hline.trans d.chosen.le_component)
    exact hv.trans (hleft.symm.le.trans inf_le_left)
  have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
    d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
  have hb : ChapterF.Source.borel L S = L ⊓ centralizer (V₁ : Set G) := by
    rw [←d.borel_eq_point_centralizer]
    unfold ChapterF.Source.borel
    rw [hleft]
  have hPC : P ≤ centralizer (V₁ : Set G) := by
    change R ⊔ S ⊔ ChapterF.Source.borel L S ≤ _
    rw [hb]
    exact sup_le (sup_le (hR.trans hHC)
      ((Global.sourceS_le_sylow d.normalizes_L hH.1.1.2).trans hTC)) inf_le_right
  have hVP : V₁ ≤ P := hVS.trans (le_sup_right.trans le_sup_left)
  have hz : V₁ ≤ (center P).map P.subtype := by
    intro x hx
    refine ⟨⟨x,hVP hx⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    apply Subtype.ext
    exact (hPC y.property x hx).symm
  refine ⟨hz,?_⟩
  intro he
  change center P = ⊥ at he
  have hv : V₁ = ⊥ := bot_unique (by simpa only [he,Subgroup.map_bot] using hz)
  have hc := d.flag.one_card
  rw [hv] at hc
  norm_num at hc

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
