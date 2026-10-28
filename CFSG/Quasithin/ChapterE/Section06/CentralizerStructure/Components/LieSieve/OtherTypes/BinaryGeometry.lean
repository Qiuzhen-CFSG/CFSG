module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Normalization
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.ModelAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.InvariantParabolics
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.BlockExclusion

/-!
# Binary invariant parabolics and the symmetric-eight exception in E.6.8

The binary components are normalized by Q. Their actual core-quotient
action is constructed and its kernel proved. In dimension four an outer
actor identifies the literal quotient with S₈; the complementary case
has inner action. The line/hyperplane and reversal-invariant paired-flag
parabolics, and their actual quotient maps, are fixed in `Parabolics`.

The paired flags generate in dimension five. In the inner-action branch
of dimension four, the line and hyperplane stabilizers generate. Their
actual quotient images are invariant under the source Sylow image, and
their lifted joins have characteristic two and no relatively subnormal
chi-zero blocks. This supplies the complete geometry contracts below.
Applying E.6.7 and deriving the final E.6.8 alternatives belongs to the
parent argument; no such exclusion is assumed in constructing these families.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
variable {G : Type*} [Group G] [Finite G] {K : GroupClass} {T : Sylow 2 G}
variable {M V U Q L : Subgroup G}

/-- The actual remaining four-dimensional cases after deriving normalization.
The inner branch still requires the parabolic construction. -/
theorem four_component_reduction (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : ClassicalGroup.IsPSL L 4 2) :
    ∃ hN : Q ≤ normalizer (L : Set G),
      (binaryAction (by decide) hm hN).range ≤ MulAut.innerSubgroup (LinearGroup 4) ∨
        Nonempty (((L ⊔ Q : Subgroup G) ⧸ pCore 2 (L ⊔ Q : Subgroup G)) ≃*
          Equiv.Perm (Fin 8)) := by
  have hN := binary_component_normalizer h hU hL hQ (Or.inl rfl) hm
  refine ⟨hN, four_quotient_alternative hm hN ?_⟩
  rw [hQ]
  exact T.isPGroup'.to_le inf_le_left

/-- In PSL₅(2), the two reversal-invariant paired flags give the required
block-free generating family in the literal component quotient. -/
theorem five_component_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : ClassicalGroup.IsPSL L 5 2) :
    Q ≤ normalizer (L : Set G) ∧ Nonempty (BlockFreeQuotientFamily Q L) := by
  have hN := binary_component_normalizer h hU hL hQ (Or.inr rfl) hm
  obtain ⟨b, hgen, hinv, hchar⟩ :=
    five_invariant_generating_parabolics h hU hL hQ hN hm
  have htwo : IsPGroup 2 Q := by
    rw [hQ]
    exact T.isPGroup'.to_le inf_le_left
  exact ⟨hN, ⟨blockFreeFamilyOfParabolics Q (by decide) hm
    (fivePairedParabolic b) hgen hinv hchar
    (fun i => fivePairedParabolic_noChiZeroBlocks hm hN htwo b i (hinv i))⟩⟩

/-- In PSL₄(2), the inner-action case supplies the block-free end-parabolic
family; an outer actor instead gives an actual isomorphism with S₈. -/
theorem four_component_geometry (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hm : ClassicalGroup.IsPSL L 4 2) :
    Q ≤ normalizer (L : Set G) ∧
      (Nonempty (BlockFreeQuotientFamily Q L) ∨
        Nonempty (((L ⊔ Q : Subgroup G) ⧸ pCore 2 (L ⊔ Q : Subgroup G)) ≃*
          Equiv.Perm (Fin 8))) := by
  obtain ⟨hN, hinner | hsym⟩ := four_component_reduction h hU hL hQ hm
  · obtain ⟨b, hgen, hinv, hchar⟩ :=
      four_inner_invariant_generating_parabolics h hU hL hQ hN hm hinner
    have htwo : IsPGroup 2 Q := by
      rw [hQ]
      exact T.isPGroup'.to_le inf_le_left
    exact ⟨hN, Or.inl ⟨blockFreeFamilyOfParabolics Q (by decide) hm
      (fourEndParabolic b) hgen hinv hchar
      (fun i => fourEndParabolic_noChiZeroBlocks hm hN htwo b i (hinv i))⟩⟩
  · exact ⟨hN, Or.inr hsym⟩

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
