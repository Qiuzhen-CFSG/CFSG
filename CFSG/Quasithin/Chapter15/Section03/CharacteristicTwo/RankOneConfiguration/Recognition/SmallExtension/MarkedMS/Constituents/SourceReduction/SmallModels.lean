module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.Constituents.SourceReduction.Interfaces
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Alternatives.Interfaces
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Coordinates
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces

/-!
# Full moved actions for the three small marked models

For actors of order 168, 360 or 6048, B.5.1(1) leaves either the original
moved space in Irr⁺ or two binary natural SL₃ copies. The degree-four and
-five cases are excluded by their actual orders. In the doubled case the
SL₃ order forces the field degree to one: a larger degree would make 64
divide the actor order. Entrywise field transport intertwines the action
on both coordinates of the full moved space; no central quotient is split.

The actual small parabolic marking gives precisely these three component
orders. At order 168 only its linear marking survives. Its node 0 is the
standard plane stabilizer and its node 1 the standard point stabilizer,
each of order 24, through the literal special-linear action map. Thus the
marked intersection has order 24 without any block or simplicity input.

These are conditional specializations of the full source conclusion and
marking. Their construction for the actual Thompson action remains with
the parent SourceReduction assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(1),
printed pp.99–103, B.5.6, p.105, and 15.3.28–31, pp.1131–1132.
The intrinsic order and field-transport calculations reuse the attributed
ATLAS ports; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
open Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem sl_card_mul (F : Type*) [Field F] [Finite F]
    (d : ℕ) [NeZero d] :
    Nat.card (Matrix.SpecialLinearGroup (Fin d) F) * (Nat.card F - 1) =
      ∏ i : Fin d, (Nat.card F ^ d - Nat.card F ^ (i : ℕ)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (center (Matrix.SpecialLinearGroup (Fin d) F)),
    Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
  exact Atlas.ExceptionalSupport.card_psl_mul d

private theorem sl_three_card (F : Type*) [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let q := Nat.card F
  have hq : 1 < q := Finite.one_lt_card
  have h := sl_card_mul F 3
  change Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) * (q - 1) = _ at h
  simp only [Fin.prod_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one] at h
  have h1 : q ^ 3 - q = q * (q ^ 2 - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    ring
  have h2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
  rw [h1, h2] at h
  apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
  rw [h]
  ring

private theorem sl_four_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  have h := sl_card_mul (ZMod 2) 4
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem sl_five_card :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  have h := sl_card_mul (ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
    Finset.prod_empty, mul_one] at h
  exact h

private theorem small_linearThree_degree (F : BinaryField)
    (hcard : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 168 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 360 ∨
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = 6048) : F.degree = 1 := by
  have hd : 2 ^ (F.degree * 3) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
    rw [sl_three_card, F.card_eq, pow_mul]
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  by_contra hn
  have hp := F.degree_pos
  have h64 : 64 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) :=
    (pow_dvd_pow 2 (show 6 ≤ F.degree * 3 by omega)).trans hd
  rcases hcard with hc | hc | hc <;> rw [hc] at h64 <;> norm_num at h64

private noncomputable def doubleFieldCoordinates (F : BinaryField) (f : F.Carrier ≃+* ZMod 2) :
    (Fin 2 → Fin 3 → F.Carrier) ≃ₗ[ZMod 2] (Fin 2 → Fin 3 → ZMod 2) :=
  let e := AddEquiv.piCongrRight (fun _ : Fin 2 =>
    AddEquiv.piCongrRight (fun _ : Fin 3 => f.toAddEquiv))
  LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap 2) e.bijective

private noncomputable def doubleFieldAction (F : BinaryField) (h : F.degree = 1) :
    ActionEquiv (repeated (linearNatural F 3) 2) (repeated binaryNatural 2) := by
  let := Fintype.ofFinite F.Carrier
  let f : F.Carrier ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two
    (by simpa only [h, pow_one, Nat.card_eq_fintype_card] using F.card_eq)).symm
  refine ⟨Atlas.fieldEquivSL 3 f, doubleFieldCoordinates F f, ?_⟩
  intro g v
  ext i j
  change f (g.val.mulVec (v i) j) =
    (g.val.map f).mulVec (fun k => f (v i k)) j
  exact RingHom.map_mulVec f.toRingHom _ _ j

/-- Specialize B.5.1(1) on its entire moved space to the three small actor orders. -/
theorem movedSmallAlternative_of_sourceConclusion {D V : Type*} [Group D] [Finite D]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (hcard : Nat.card L = 168 ∨ Nat.card L = 360 ∨ Nat.card L = 6048)
    (h : QuasisimpleSourceConclusion ρ L) : MovedSmallAlternative ρ L := by
  cases h.clause_one with
  | irreducible hi _ _ _ _ =>
    exact .single (h.sectionData.space_eq ▸ hi)
  | doubleThree F _ e _ _ =>
    have hn := small_linearThree_degree F (by
      simpa only [Nat.card_congr e.groupEquiv.toEquiv] using hcard)
    let a := doubleFieldAction F hn
    refine .double h.sectionData.space h.sectionData.space_eq
      ⟨e.groupEquiv.trans a.groupEquiv, e.linearEquiv.trans a.linearEquiv, ?_⟩
    intro g v
    change a.linearEquiv (e.linearEquiv _) = _
    rw [e.intertwines]
    exact a.intertwines _ _
  | naturalDual d hd _ hn =>
    obtain ⟨e⟩ := hn
    have hc := Nat.card_congr e.groupEquiv.toEquiv
    rcases hd with rfl | rfl
    · change Nat.card L = Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) at hc
      rw [sl_four_card] at hc
      rcases hcard with hh | hh | hh <;> omega
    · change Nat.card L = Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) at hc
      rw [sl_five_card] at hc
      rcases hcard with hh | hh | hh <;> omega
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨e⟩ := hn
    have hc := Nat.card_congr e.groupEquiv.toEquiv
    rcases hd with rfl | rfl
    · change Nat.card L = Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) at hc
      rw [sl_four_card] at hc
      rcases hcard with hh | hh | hh <;> omega
    · change Nat.card L = Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) at hc
      rw [sl_five_card] at hc
      rcases hcard with hh | hh | hh <;> omega


private theorem symplectic_derived_card :
    Nat.card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) = 360 := by
  rw [Nat.card_congr (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
    (F := ZMod 2) (by simp)).toEquiv, nat_card_alternatingGroup]
  norm_num

private theorem g2_derived_card :
    Nat.card (commutator (Atlas.G2.Model (ZMod 2))) = 6048 := by
  rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
  exact Atlas.G2.BinaryException.card_H

open BinaryLinear.InvariantNodeActions BinaryLinear.OuterCyclic Parabolics

private theorem cut_zero_mem (v : Fin 3 → ZMod 2) :
    v ∈ cutSpace (Pi.basisFun (ZMod 2) (Fin 3)) (0 : Fin 2) ↔ v 1 = 0 ∧ v 2 = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq, Fin.val_zero]
  constructor
  · intro h
    constructor
    · by_contra hn
      exact (by decide : ¬ (1 : Fin 3).val ≤ 0) (h 1 hn)
    · by_contra hn
      exact (by decide : ¬ (2 : Fin 3).val ≤ 0) (h 2 hn)
  · rintro ⟨h1, h2⟩ i hi
    fin_cases i <;> simp_all

private theorem cut_one_mem (v : Fin 3 → ZMod 2) :
    v ∈ cutSpace (Pi.basisFun (ZMod 2) (Fin 3)) (1 : Fin 2) ↔ v 2 = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Pi.basisFun_repr,
    Set.mem_ofPred_eq, Fin.val_one]
  constructor
  · intro h
    by_contra hn
    exact (by decide : ¬ (2 : Fin 3).val ≤ 1) (h 2 hn)
  · intro hv i hi
    fin_cases i <;> simp_all

private theorem linearThreeParabolic_zero :
    linearThreeParabolic 0 = Matrix.PSL3Two.lineParabolicSL := by
  ext g
  change slEquivLinear 3 g ∈ minimalParabolic (Pi.basisFun (ZMod 2) (Fin 3)) 0 ↔ _
  rw [minimalParabolic, mem_cutStabilizer_maps, Matrix.PSL3Two.lineParabolicSL,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ i ∈ ({0} : Set (Fin 2))ᶜ, ∀ v ∈ cutSpace _ i,
    slEquivLinear 3 g v ∈ cutSpace _ i) ↔
      (∀ ⦃v : Fin 3 → ZMod 2⦄, v 2 = 0 → (g.val.mulVec v) 2 = 0)
  constructor
  · intro h v hv
    exact (cut_one_mem _).mp (h 1 (by decide) v ((cut_one_mem v).mpr hv))
  · intro h i hi v hv
    fin_cases i
    · exact (hi rfl).elim
    · exact (cut_one_mem _).mpr (h ((cut_one_mem v).mp hv))

private theorem linearThreeParabolic_one :
    linearThreeParabolic 1 = Matrix.PSL3Two.pointParabolicSL := by
  ext g
  change slEquivLinear 3 g ∈ minimalParabolic (Pi.basisFun (ZMod 2) (Fin 3)) 1 ↔ _
  rw [minimalParabolic, mem_cutStabilizer_maps, Matrix.PSL3Two.pointParabolicSL,
    MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ i ∈ ({1} : Set (Fin 2))ᶜ, ∀ v ∈ cutSpace _ i,
    slEquivLinear 3 g v ∈ cutSpace _ i) ↔
      (∀ ⦃v : Fin 3 → ZMod 2⦄, v 1 = 0 ∧ v 2 = 0 →
        (g.val.mulVec v) 1 = 0 ∧ (g.val.mulVec v) 2 = 0)
  constructor
  · intro h v hv
    exact (cut_zero_mem _).mp (h 0 (by decide) v ((cut_zero_mem v).mpr hv))
  · intro h i hi v hv
    fin_cases i
    · exact (cut_zero_mem _).mpr (h ((cut_zero_mem v).mp hv))
    · exact (hi rfl).elim

/-- Both node conventions give actual order-24 matrix stabilizers. -/
theorem linearThreeParabolic_card (i : Fin 2) : Nat.card (linearThreeParabolic i) = 24 := by
  fin_cases i
  · change Nat.card (linearThreeParabolic 0) = 24
    rw [linearThreeParabolic_zero]
    exact Matrix.PSL3Two.card_lineParabolicSL
  · change Nat.card (linearThreeParabolic 1) = 24
    rw [linearThreeParabolic_one]
    exact Matrix.PSL3Two.card_pointParabolicSL

variable {G : Type*} [Group G]

/-- The actual carriers in a small marking have orders 168, 360 and 6048. -/
theorem marked_star_card (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hm : SmallParabolicMarking d I c.L) :
    Nat.card (d.starImage I c.L) = 168 ∨ Nat.card (d.starImage I c.L) = 360 ∨
      Nat.card (d.starImage I c.L) = 6048 := by
  cases hm with
  | linearThree m =>
    exact Or.inl ((Nat.card_congr m.equiv.toEquiv).trans Matrix.PSL3Two.card_SL)
  | symplecticDerived m =>
    exact Or.inr (Or.inl ((Nat.card_congr m.equiv.toEquiv).trans symplectic_derived_card))
  | g2Derived m =>
    exact Or.inr (Or.inr ((Nat.card_congr m.equiv.toEquiv).trans g2_derived_card))

/-- At order 168 the literal marked component intersection has order 24.
Only the marking and intrinsic model orders enter this comparison. -/
theorem marked_intersection_card_of_star_card (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hm : SmallParabolicMarking d I c.L)
    (hc : Nat.card (d.starImage I c.L) = 168) :
    Nat.card ((d.starImage I (d.M ⊓ c.L)).subgroupOf (d.starImage I c.L)) = 24 := by
  cases hm with
  | linearThree m =>
    have h := linearThreeParabolic_card m.node
    rw [← m.intersection, card_map_of_injective m.equiv.injective] at h
    exact h
  | symplecticDerived m =>
    have h := (Nat.card_congr m.equiv.toEquiv).trans symplectic_derived_card
    omega
  | g2Derived m =>
    have h := (Nat.card_congr m.equiv.toEquiv).trans g2_derived_card
    omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.Constituents.SourceReduction
