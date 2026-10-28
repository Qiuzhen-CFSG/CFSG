module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.Definitions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Action
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.SylowTwoPart
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Counting the full centralizer against its intersection with max4

The certified max4 order divisor and the 168 automorphisms of its normal
eight give at least 3932160 elements in its relative centralizer. A matching
upper bound for the full ambient centralizer therefore forces containment.

For that upper bound, the marking places every centralizing element in the
full centralizer C(t), which is the original max2 word subgroup by the
certified generation theorem. Distinct conjugate pairs give 5544 disjoint
translates of their common centralizer. Since |C(t)| = 21799895040, its pair
centralizer has order at most 3932160. The marking and pair-orbit witnesses
remain explicit independent premises; the relative lower bound is unconditional.

Source context: Kleidman–Wilson (1988), pp.484–510, and the J4 branch of
Aschbacher–Smith A.3.12. The literal ATLAS programs and matrix provenance are
retained by the imported NormalEight and TwoCoreCentralizer modules.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
attribute [local irreducible] modelGroup matrixA matrixB

private theorem source_eq_centralizer : sourceSubgroup = centralizer ({t} : Set Model) := by
  have hmap : sourceSubgroup.map (MulAut.conj h⁻¹).toMonoidHom =
      centralizer ({a} : Set Model) := by
    rw [sourceSubgroup_map_conj, localSubgroup_eq_top, ← MonoidHom.range_eq_map,
      centralizerToModel_range]
  ext g
  have hm : g ∈ sourceSubgroup ↔ (MulAut.conj h⁻¹) g ∈
      centralizer ({a} : Set Model) := by
    rw [← hmap]
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [hm, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have ht : (MulAut.conj h⁻¹) t = a := by
    simpa only [MulAut.conj_apply, inv_inv] using conjugates_t
  rw [← ht, ← map_mul, ← map_mul]
  exact (MulAut.conj h⁻¹).injective.eq_iff

private theorem source_card : Nat.card sourceSubgroup = 21799895040 := by
  rw [card_sourceSubgroup_eq_localSubgroup, localSubgroup_eq_top, card_top]
  exact Janko4.OuterReduction.OddIndex.centralizer_card

private abbrev pairCentralizer : Subgroup sourceSubgroup :=
  centralizer ({sourceP, sourceQ} : Set sourceSubgroup)

private theorem pairOrbit_mul (g : sourceSubgroup) (c : pairCentralizer) :
    pairOrbit (g * c) = pairOrbit g := by
  have hp := c.property sourceP (by simp)
  have hq := c.property sourceQ (by simp)
  have fixed (p : sourceSubgroup) (hc : p * (c : sourceSubgroup) = c * p) :
      (MulAut.conj (c : sourceSubgroup)) p = p := by
    simp only [MulAut.conj_apply, ← hc, mul_inv_cancel_right]
  change ((MulAut.conj (g * c)) sourceP, (MulAut.conj (g * c)) sourceQ) = _
  rw [map_mul]
  change ((MulAut.conj g) ((MulAut.conj (c : sourceSubgroup)) sourceP),
    (MulAut.conj g) ((MulAut.conj (c : sourceSubgroup)) sourceQ)) = _
  rw [fixed sourceP hp, fixed sourceQ hq]
  rfl

private theorem pairCentralizer_card_le (ho : PairOrbitWitness) :
    Nat.card pairCentralizer ≤ 3932160 := by
  obtain ⟨w, hw⟩ := ho
  let f : Fin 5544 × pairCentralizer → sourceSubgroup := fun x => w x.1 * x.2
  have hf : Function.Injective f := by
    rintro ⟨i, c⟩ ⟨j, d⟩ hij
    have he : i = j := hw (by
      simpa only [f, pairOrbit_mul] using congrArg pairOrbit hij)
    subst j
    have hcd : c = d := Subtype.ext (mul_left_cancel hij)
    subst d
    rfl
  have hc := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_fin, source_card] at hc
  omega

private theorem element_mem (i : Fin 8) : (NormalEight.element i : Model) ∈ max4Eight :=
  mem_map_of_mem _ (show NormalEight.element i ∈ NormalEight.eight from ⟨i, rfl⟩)

private theorem conjugate_commute_of_marking (hm : Marking)
    (c : centralizer (max4Eight : Set Model)) :
    let z := (MulAut.conj bridge) (c : Model)
    z * t = t * z ∧ z * (sourceP : Model) = sourceP * z ∧
      z * (sourceQ : Model) = sourceQ * z := by
  have hc (i : Fin 8) :
      (MulAut.conj bridge) (c : Model) * (MulAut.conj bridge) (NormalEight.element i : Model) =
      (MulAut.conj bridge) (NormalEight.element i : Model) * (MulAut.conj bridge) (c : Model) := by
    simpa only [map_mul] using
      congrArg (MulAut.conj bridge) (c.property _ (element_mem i)).symm
  exact ⟨hm.2.1 ▸ hc 2, hm.1 ▸ hc 1, hm.2.2 ▸ hc 3⟩

/-- The finite marking and pair orbit bound the full ambient centralizer. -/
theorem centralizer_card_le (hm : Marking) (ho : PairOrbitWitness) :
    Nat.card (centralizer (max4Eight : Set Model)) ≤ 3932160 := by
  let f : centralizer (max4Eight : Set Model) → pairCentralizer := fun c =>
    ⟨⟨(MulAut.conj bridge) (c : Model), by
      rw [source_eq_centralizer, mem_centralizer_singleton_iff]
      exact (conjugate_commute_of_marking hm c).1⟩, by
      intro p hp
      rcases hp with rfl | rfl
      · exact Subtype.ext (conjugate_commute_of_marking hm c).2.1.symm
      · exact Subtype.ext (conjugate_commute_of_marking hm c).2.2.symm⟩
  have hf : Function.Injective f := by
    intro c d he
    apply Subtype.ext
    apply (MulAut.conj bridge).injective
    exact congrArg (fun x : pairCentralizer => ((x : sourceSubgroup) : Model)) he
  exact (Nat.card_le_card_of_injective f hf).trans (pairCentralizer_card_le ho)

/-- The literal max4 centralizer already contains at least 3932160 elements. -/
theorem relative_centralizer_card_ge : 3932160 ≤ Nat.card ((centralizer (max4Eight : Set Model)).subgroupOf max4Subgroup) := by
  let := NormalEight.elementary_eight
  let : IsElementaryAbelian 2 max4Eight := IsElementaryAbelian.map_subtype
  have hE : Nat.card max4Eight = 8 :=
    (Nat.card_congr (NormalEight.eight.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm.trans
      NormalEight.card_eight
  have hAut : Nat.card (MulAut max4Eight) = 168 := card_mulAut_of_elementary_eight _ hE
  let f : max4Subgroup →* MulAut max4Eight :=
    max4Eight.normalizerMonoidHom.comp (inclusion max4_le_eight_normalizer)
  have hker : f.ker = (centralizer (max4Eight : Set Model)).subgroupOf max4Subgroup := by
    ext g
    change (inclusion max4_le_eight_normalizer g) ∈ max4Eight.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    rfl
  have hr : Nat.card f.range ≤ 168 := f.range.card_le_card_group.trans_eq hAut
  have hc : 660602880 ≤ Nat.card max4Subgroup := by
    apply Nat.le_of_dvd Nat.card_pos
    exact max4_localOrder_dvd_of_seed_card max4Projection max4Projection_surjective
      CharacteristicTwo.seedNormalClosure_isPGroup
      (SylowTwoPart.seed_card_lower_of_coordinates
        CharacteristicTwo.seedConjugate_coordinates)
  have hm := f.ker.card_mul_index
  rw [index_ker, hker] at hm
  nlinarith

/-- The matching full ambient upper bound forces centralizer containment. -/
theorem centralizer_le_of_card_le
    (hc : Nat.card (centralizer (max4Eight : Set Model)) ≤ 3932160) :
    centralizer (max4Eight : Set Model) ≤ max4Subgroup := by
  have hl : 3932160 ≤ Nat.card (centralizer (max4Eight : Set Model) ⊓ max4Subgroup : Subgroup Model) := by
    rw [← subgroupOf_map_subtype, card_map_of_injective Subtype.val_injective]
    exact relative_centralizer_card_ge
  have he := eq_of_le_of_card_ge (H := centralizer (max4Eight : Set Model) ⊓ max4Subgroup)
    (K := centralizer (max4Eight : Set Model)) inf_le_left (hc.trans hl)
  rw [← he]
  exact inf_le_right

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer
