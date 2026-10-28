module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.LocalCover.Contracts
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.Inputs
public import Theory.GroupTheory.PGroup.NormalPrimeImage

/-!
# Excluding the extraspecial residual before product generation

The component residual A is normal in Y and |A/O₂(A)|=3. Its image in the
three-group Y/O₂(Y) is therefore central. In the extraspecial alternative
of 15.3.7, the literal inverse image of this centre is C_Y(V). That would
make A centralize the plane it moves, a contradiction. Thus the full E₉
alternative follows without assuming Y₊=A⟨y⟩ or any centre calculation
for the component. Both choices of the original plane labels are retained.

Source: Aschbacher--Smith, 15.3.7 and the proof of 15.3.38,
combined manuscript (1 March 2004), printed pp.1122 and 1136.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
variable {G : Type*} [Group G] [Finite G]

/-- The central-preimage clause of the extraspecial alternative is incompatible
with a normal cyclic residual moving a nontrivial plane. -/
theorem not_central_preimage_of_moving_plane {Y A V W : Subgroup G}
    (hAY : A ≤ Y) (hYA : Y ≤ normalizer (A : Set G))
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hA : Nat.card (A ⧸ pCore 2 A) = 3)
    (hWV : W ≤ V) (hW : W ≠ ⊥) (hmoves : ⁅W, A⁆ = W) :
    (centralPreimage (pCore 2 Y)).map Y.subtype ≠
      Y ⊓ centralizer (V : Set G) := by
  intro he
  have hc := image_core_quotient_le_center hAY hYA hY (show
    Nat.card (A ⧸ pCore 2 A) ∣ 3 by rw [hA])
  have hAC : A ≤ centralizer (V : Set G) := by
    intro a ha
    have hz : (⟨a, hAY ha⟩ : Y) ∈ centralPreimage (pCore 2 Y) :=
      hc (mem_map_of_mem _ ha)
    exact (he ▸ mem_map_of_mem Y.subtype hz).2
  have hzero : ⁅W, A⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hWV.trans (le_centralizer_iff.mp hAC))
  exact hW (hmoves.symm.trans hzero)

/-- The full elementary alternative of 15.3.7, deduced from the constructed
oriented Borel planes and the source three-group alternatives. -/
theorem OrientedBorelData.elementaryAlternative
    {d : CharacteristicTwo.LocalData G} {L : Subgroup G} {n : ℕ}
    {c : ProjectiveMarking L (2 ^ n)}
    (b : OrientedBorelData d.M d.Yplus d.S L d.V₁ d.V₂ c)
    (hplus : d.Yplus = d.Y) (hn : d.Y ≤ normalizer (L : Set G))
    (hthree : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y))
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action) :
    ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V := by
  rcases h7 with h | h
  · exact h
  · have hWV : b.W₂ ≤ d.V := by
      rcases b.planes with ⟨_, h₂⟩ | ⟨_, h₂⟩
      · rw [h₂]
        exact d.action.plane_le _
      · rw [h₂]
        exact d.action.plane_le _
    have hW : b.W₂ ≠ ⊥ := by
      intro he
      have hc := b.second_card
      rw [he] at hc
      norm_num at hc
    have hA := b.component_quotient
    have hmoves := b.component_moves
    have hApart : componentPart d.Yplus L = componentPart d.Y L :=
      congrArg (fun X => componentPart X L) hplus
    rw [hApart] at hA hmoves
    exact False.elim (not_central_preimage_of_moving_plane
      (RankTwo.componentFactor_le_left d.Y L)
      (ComponentIntersection.normalizes_intersectionResidual hn)
      hthree hA hWV hW hmoves h.2.1)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.LocalCover
