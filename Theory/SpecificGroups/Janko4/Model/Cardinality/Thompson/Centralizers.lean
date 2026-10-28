module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.Reduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound
public import Theory.GroupTheory.TwoInvolutionClassLocalBounds

/-!
# Full-centralizer transport for the J₄ involution census

The max2 generation theorem identifies the census carrier with the full
centralizer of the first matrix generator. Matching local lower and ambient
upper bounds identify the seed centralizer inside literal max1 with its full
centralizer in `Model`. The equivalences preserve the actual inclusions.

Transporting the certified product slices and local conjugacy classes through
these equivalences supplies the finite inputs to the refined Thompson bound.
The two representatives are separated by the certified displacement ranks;
odd index and the checked max1 fusion cover every ambient involution.
No simplicity, global order, or ambient class-table identification is assumed.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, A.6.1–4, printed pp.64–65.
The finite matrix and word certificates retain their ATLAS attribution in
the imported local census and centralizer modules.
-/

public section
namespace Janko4.Cardinality.Thompson
open LocalInvolutionCensus
open Theory.GroupTheory.TwoInvolutionClassLocalBounds
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData hiding t
open LocalStructure.MathieuSeedCentralizer

attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernelSeed

/-- The actual max2 census carrier is the full centralizer of its marked involution. -/
noncomputable def max2EquivCentralizer : H ≃* Centralizer z :=
  ((MulEquiv.subgroupCongr localSubgroup_eq_top).trans Subgroup.topEquiv).trans
    ((MonoidHom.ofInjective centralizerToModel_injective).trans
      (MulEquiv.subgroupCongr centralizerToModel_range))

/-- This equivalence preserves the original embedding into the matrix model. -/
@[simp] theorem max2EquivCentralizer_coe (u : H) :
    (max2EquivCentralizer u : Model) = eH u := by rfl

/-- The marked local involution maps to the marked ambient generator. -/
@[simp] theorem max2EquivCentralizer_zH :
    (max2EquivCentralizer zH : Model) = z := by rfl

/-- Exact order of the full first involution centralizer. -/
theorem centralizer_z_card : Nat.card (Centralizer z) = 21799895040 :=
  OuterReduction.OddIndex.modelCentralizer_card

/-- The census carrier has the same exact order as the full centralizer. -/
theorem max2_card : Nat.card H = 21799895040 :=
  (Nat.card_congr max2EquivCentralizer.toEquiv).trans centralizer_z_card

/-- Matching proved bounds give the exact order of the full seed centralizer. -/
theorem centralizer_t_card : Nat.card (Centralizer t) = 1816657920 :=
  Nat.le_antisymm ambientSeedCentralizer_card_le
    (ambientSeedCentralizer_card_ge matrixA_mul_self matrixB_pow_four)

private def seedCentralizerMap :
    InvolutionBound.centralizer matrixA_mul_self matrixB_pow_four →* Centralizer t where
  toFun u := ⟨InvolutionBound.inclusion matrixA_mul_self matrixB_pow_four u,
    map_localSeedCentralizer_le matrixA_mul_self matrixB_pow_four
      ⟨u.val, u.property, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem seedCentralizerMap_bijective : Function.Bijective seedCentralizerMap := by
  constructor
  · intro u v he
    exact Subtype.ext (Subtype.ext (congrArg (fun w : Centralizer t => (w : Model)) he))
  · intro u
    have hu := ambientSeedCentralizer_le_max1_of_card_le
      matrixA_mul_self matrixB_pow_four ambientSeedCentralizer_card_le u.property
    let v : max1Subgroup matrixA_mul_self matrixB_pow_four := ⟨u.val, hu⟩
    have hv : v ∈ InvolutionBound.centralizer matrixA_mul_self matrixB_pow_four := by
      intro w hw
      obtain rfl := Set.mem_singleton_iff.mp hw
      apply Subtype.ext
      exact u.property _ (Set.mem_singleton _)
    exact ⟨⟨v, hv⟩, rfl⟩

/-- The seed centralizer inside literal max1 is the full ambient centralizer. -/
noncomputable def seedEquivCentralizer :
    InvolutionBound.centralizer matrixA_mul_self matrixB_pow_four ≃* Centralizer t :=
  MulEquiv.ofBijective seedCentralizerMap seedCentralizerMap_bijective

/-- The seed equivalence preserves the literal inclusion into `Model`. -/
@[simp] theorem seedEquivCentralizer_coe
    (u : InvolutionBound.centralizer matrixA_mul_self matrixB_pow_four) :
    (seedEquivCentralizer u : Model) =
      InvolutionBound.inclusion matrixA_mul_self matrixB_pow_four u := by rfl

/-- The second representative is an involution by the certified word fusion. -/
theorem orderOf_t : orderOf t = 2 :=
  InvolutionBound.seed_order matrixA_mul_self matrixB_pow_four

private theorem old_a_eq : Simplicity.a matrixA_mul_self = Janko4.a := by
  apply toMatrix_injective
  rfl

private theorem old_b_eq : Simplicity.b matrixB_pow_four = Janko4.b := by
  apply toMatrix_injective
  rfl

/-- Odd index and actual max1 fusion cover all ambient involutions. -/
theorem involution_classes (u : Model) (hu : orderOf u = 2) :
    IsConj z u ∨ IsConj t u := by
  obtain hz | ht := OuterReduction.involution_isConj_of_max1_odd_index
    OuterReduction.max1_odd_index_unconditional hu
  · exact Or.inl hz
  · obtain ⟨g, hg⟩ := Simplicity.Max1Fusion.seed_fuses_second matrixA_mul_self matrixB_pow_four
    have hw : Simplicity.word (Simplicity.a matrixA_mul_self)
        (Simplicity.b matrixB_pow_four) "ababb" =
        Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
      rw [old_a_eq, old_b_eq]
      simp [Simplicity.word, mul_assoc]
    rw [hw] at hg
    exact Or.inr ((isConj_iff.mpr ⟨g, hg.symm⟩).trans ht)

private noncomputable def max2SliceEquiv (p q : Model) :
    {u : H // IsConj p (eH u) ∧ IsConj q (eH (u * zH))} ≃ Slice z p q :=
  max2EquivCentralizer.toEquiv.subtypeEquiv (fun u => by
    simp only [map_mul]
    rfl)

/-- The certified A,A count transported to the full first centralizer. -/
theorem slice_aa_card_le : Nat.card (Slice z z z) ≤ 112266 := by
  rw [← Nat.card_congr (max2SliceEquiv z z)]
  exact aa_card_le max2_card.le

/-- The certified B,A count transported to the full first centralizer. -/
theorem slice_ba_card_le : Nat.card (Slice z t z) ≤ 81840 := by
  rw [← Nat.card_congr (max2SliceEquiv t z)]
  exact ba_card_le max2_card.le

/-- The three actual representatives in the full-centralizer B,B slice. -/
noncomputable def bbCover (i : Fin 3) : Slice z t t :=
  max2SliceEquiv t t ⟨bbRepresentative i, bbRepresentative_mem_bb i⟩

/-- The cover retains conjugacy inside the full centralizer. -/
theorem bbCover_covers (u : Slice z t t) : ∃ i, IsConj (bbCover i).val u.val := by
  obtain ⟨v, rfl⟩ := (max2SliceEquiv t t).surjective u
  obtain ⟨i, hi⟩ := bb_coverage max2_card.le v.property
  exact ⟨i, max2EquivCentralizer.toMonoidHom.map_isConj hi⟩

private noncomputable def max2ClassEquiv (u : H) :
    localClass u ≃ LocalOrbit (max2EquivCentralizer u) :=
  max2EquivCentralizer.toEquiv.subtypeEquiv (fun v => by
    constructor
    · exact max2EquivCentralizer.toMonoidHom.map_isConj
    · intro h
      have hr := max2EquivCentralizer.symm.toMonoidHom.map_isConj h
      change IsConj (max2EquivCentralizer.symm (max2EquivCentralizer u))
        (max2EquivCentralizer.symm (max2EquivCentralizer v)) at hr
      rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at hr
      exact hr)

/-- The three full-centralizer orbit bounds, in the certified representative order. -/
theorem bbCover_card_le (i : Fin 3) :
    Nat.card (LocalOrbit (bbCover i).val) ≤ ![2772, 221760, 532224] i := by
  change Nat.card (LocalOrbit (max2EquivCentralizer (bbRepresentative i))) ≤ _
  rw [← Nat.card_congr (max2ClassEquiv (bbRepresentative i))]
  exact bbRepresentative_class_card_le max2_card.le i

/-- The local seed-type count applies to the full ambient seed centralizer. -/
theorem seed_type_card_le : Nat.card {u : Centralizer t // IsConj t (u : Model)} ≤ 262144 := by
  have hn : ¬ IsConj (Simplicity.a matrixA_mul_self)
      (localKernelSeed matrixA_mul_self matrixB_pow_four : Model) := by
    rw [old_a_eq]
    exact not_isConj_z_t
  have he : InvolutionBound.SeedType matrixA_mul_self matrixB_pow_four ≃
      {u : Centralizer t // IsConj t (u : Model)} :=
    seedEquivCentralizer.toEquiv.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Nat.card_congr he]
  exact InvolutionBound.seedType_card_le matrixA_mul_self matrixB_pow_four hn

end Janko4.Cardinality.Thompson
