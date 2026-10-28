module
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.EightTransport
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.PerfectSeeds
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Suzuki.Commutation
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.UnipotentCenter.Centrality
public import Theory.GroupTheory.PerfectCentralizerLift.Preimage
-- Internal extension of the positive-root calculus: only its geometric
-- lemmas are used in private proofs; the public boundary uses actual subgroups.
import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.RootCalculus

/-!
# Class-two lifts of the fifth Ree root block

The commutator of two fifth-block elements lies in its central curve Y5.
That curve centralizes the whole Suzuki-side seed: the positive root
calculation and the commuting orthogonal signed B2 planes prove this
inside the literal matrix model. The seed is perfect for m>=1, so its
centralizer lifts across every central extension. Thus arbitrary lifts
of the fifth root block have class two, including the field-eight case.

Source: GLS3 Table 2.4 and 2.4.5(d); Aschbacher--Smith I.1.1--4,
printed pp.407--408. The resulting ambient identity supplies precisely
the exceptional Suzuki-root splitting premise in the Ree cover argument.
-/

public section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open scoped commutatorElement
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.EightAmbient
open Parabolics LargeLocalSeeds ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations.LongCommutators
noncomputable section
private local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem central_four (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = rootGeneratorInGroup m (R 15) t *
      rootGeneratorInGroup m (R 14) (Parabolics.RadicalCoordinates.FixedCoordinates.halfFrobenius m t) := by
  simp only [centralWord, rootFieldEnd, if_pos (MatrixRelations.longRoot_isLong 4),
    Parabolics.RadicalCoordinates.FixedCoordinates.halfFrobenius]
  rfl

private theorem top_commute_positive (m : ℕ) (i : Fin 24) (hi : i = 14 ∨ i = 15)
    (r : F4Chevalley.Root) (hr : typeF4RootPairing_base.IsPos r)
    (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (R i) a) (rootGeneratorInGroup m r b) := by
  apply curve_commute_nonneg m _ _ (rpos i) hr
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := typeF4RootPairing_base.exists_root_eq_sum_int r
  have hf : 0 < f := by
    apply hf₁.resolve_right
    rw [RootPairing.Base.isPos_iff, RootPairing.Base.height_eq_sum hf₂] at hr
    contrapose! hr
    exact Finset.sum_nonpos fun j _ => hr.le j
  have hn (j : F4Chevalley.Root) (hj : j ∈ typeF4RootPairing_base.support) :
      0 ≤ dot (R i).val (typeF4RootPairing.root j) := by
    change j ∈ (typeF4RootPairing_base.support : Set F4Chevalley.Root) at hj
    rw [typeF4RootPairing_base_support] at hj
    obtain ⟨k,rfl⟩ := hj
    rw [rval]
    rcases hi with rfl | rfl <;> fin_cases k <;>
      norm_num [V, typeF4RootPairing_root, typeF4SimpleRootIndex_val,
        typeF4SimpleRoot, dot, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  change 0 ≤ (R i).val ⬝ᵥ typeF4RootPairing.root r
  rw [hf₂, dotProduct_sum]
  apply Finset.sum_nonneg
  intro j hj
  rw [dotProduct_smul]
  exact smul_nonneg (hf.le j) (hn j hj)

private theorem top_commute_negative_middle (m : ℕ) (i : Fin 24)
    (hi : i = 14 ∨ i = 15) (j : Fin 4) (hj : j ∈ leviNodes .suzuki)
    (a b : CoefficientField m) :
    Commute (rootGeneratorInGroup m (R i) a)
      (rootGeneratorInGroup m (-typeF4SimpleRootIndex j) b) := by
  apply Commute.symm
  apply OddPrimary.SuzukiOrthogonal.root_commute
  · have hj' : j = 1 ∨ j = 2 := by simpa [leviNodes] using hj
    have hv (r : F4Chevalley.Root) : (-r).val = -r.val := by
      change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
      simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self]
    rw [hv]
    rcases hj' with rfl | rfl <;>
      norm_num [typeF4SimpleRootIndex_val, typeF4SimpleRoot, Matrix.cons_val_two,
        Matrix.cons_val_three]
  · rw [rval]
    rcases hi with rfl | rfl <;> norm_num [V, Matrix.cons_val_two, Matrix.cons_val_three]


/-- The central fifth curve centralizes the entire actual Suzuki-side seed. -/
theorem central_fifth_commute_seed (m : ℕ) (t : CoefficientField m)
    (x : Model m) (hx : x ∈ seed m .suzuki) :
    Commute (centralElement m 4 t) x := by
  have hle : splitSeed m .suzuki ≤
      centralizer ({centralWord m 4 t} : Set (SplitGroup m)) := by
    apply (closure_le _).mpr
    rintro _ ⟨r,b,hr,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [central_four]
    rcases hr with hpos | ⟨j,hj,rfl⟩
    · exact ((top_commute_positive m 15 (.inr rfl) r hpos t b).mul_left
        (top_commute_positive m 14 (.inl rfl) r hpos (RadicalCoordinates.FixedCoordinates.halfFrobenius m t) b)).eq.symm
    · exact ((top_commute_negative_middle m 15 (.inr rfl) j hj t b).mul_left
        (top_commute_negative_middle m 14 (.inl rfl) j hj (RadicalCoordinates.FixedCoordinates.halfFrobenius m t) b)).eq.symm
  apply Commute.of_map (toSplitGroup_injective m)
  rw [centralElement_coe]
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

private theorem block_commutator (m : ℕ) (a b c d : CoefficientField m) :
    ⁅blockPoint m 4 a b, blockPoint m 4 c d⁆ =
      centralElement m 4 (titsEnd m a * c + titsEnd m c * a) := by
  let z := centralElement m 4 (titsEnd m a * c + titsEnd m c * a)
  have hz : blockPoint m 4 a b * blockPoint m 4 c d =
      z * (blockPoint m 4 c d * blockPoint m 4 a b) := by
    rw [blockPoint_mul m 4 (by decide), blockPoint_mul m 4 (by decide)]
    dsimp only [blockPoint, z]
    rw [← mul_assoc, ← (main_central_commute m 4 (by decide) (c+a)
      (titsEnd m a * c + titsEnd m c * a)).eq, mul_assoc,
      ← centralElement_add m 4 (by decide)]
    congr 1
    · congr 1; exact add_comm a c
    · congr 1
      rw [add_assoc (titsEnd m a * c), ← add_assoc (titsEnd m c * a),
        CharTwo.add_self_eq_zero, zero_add]
      ring
  change _ = z
  rw [commutatorElement_def, hz]
  group

/-- Commutators inside the fifth block lie in the central fifth curve. -/
theorem commutator_mem_Y_fifth (m : ℕ) (a b : Model m)
    (ha : a ∈ ElementaryTwoBound.X m 4) (hb : b ∈ ElementaryTwoBound.X m 4) :
    ⁅a,b⁆ ∈ ElementaryTwoBound.Y m 4 := by
  obtain ⟨s,t,rfl⟩ := (mem_X_even m 4 (by decide) a).mp ha
  obtain ⟨u,v,rfl⟩ := (mem_X_even m 4 (by decide) b).mp hb
  rw [block_commutator]
  exact centralElement_mem_Y m 4 _


/-- Arbitrary lifts of the fifth block have class two in every central
extension of the actual Ree group. -/
theorem fifth_triple_commutator_eq_one (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] (f : E →* Model m) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (a b c : E)
    (ha : f a ∈ ElementaryTwoBound.X m 4)
    (hb : f b ∈ ElementaryTwoBound.X m 4)
    (hc : f c ∈ ElementaryTwoBound.X m 4) : ⁅⁅a,b⁆,c⁆ = 1 := by
  let : Group.IsPerfect (seed m .suzuki) := Parabolics.OuterLocal.seed_perfect hm .suzuki
  have hcomm : f ⁅a,b⁆ ∈ ElementaryTwoBound.Y m 4 := by
    rw [map_commutatorElement]
    exact commutator_mem_Y_fifth m _ _ ha hb
  obtain ⟨t,ht⟩ := (mem_Y_iff m 4 (by decide) _).mp hcomm
  have hcent : f ⁅a,b⁆ ∈ centralizer (seed m .suzuki : Set (Model m)) := by
    rw [← ht]
    apply mem_centralizer_iff.mpr
    intro x hx
    exact (central_fifth_commute_seed m t x hx).eq.symm
  have hcseed : f c ∈ seed m .suzuki :=
    unipotent_le_seed m .suzuki (X_le_unipotent m 4 hc)
  exact (PerfectCentralCovering.commute_of_centralizing_image_of_perfect f hf hk
    (seed m .suzuki) ⁅a,b⁆ c hcent hcseed).commutator_eq


/-- The actual embedded Suzuki root group has class-two preimage, including
in the exceptional field-eight central extension. -/
theorem liftedRootClassTwo {E : Type*} [Group E]
    (f : E →* Model 1) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    LiftedRootClassTwo 1 f :=
  liftedRootClassTwo_of_fifth_block f hf
    (fifth_triple_commutator_eq_one 1 (by decide) f hf hk)

/-- The exact degree-two-cover obligation consumed by the Ree two-primary
kernel exclusion. In fact the argument works for every central kernel. -/
theorem triple_commutator_eq_one {E : Type*} [Group E] [Finite E]
    (d : PerfectCentralCovering.Cover E (Model 1))
    (_hd : Nat.card d.toMonoidHom.ker = 2) (a b c : E)
    (ha : d.toMonoidHom a ∈ (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup 1).map
      (suzukiEmbedding 1))
    (hb : d.toMonoidHom b ∈ (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup 1).map
      (suzukiEmbedding 1))
    (hc : d.toMonoidHom c ∈ (BenderSuzuki.MatrixGroups.SuzukiRootSubgroup 1).map
      (suzukiEmbedding 1)) : ⁅⁅a,b⁆,c⁆ = 1 :=
  liftedRootClassTwo d.toMonoidHom d.surjective d.ker_le_center a b c ha hb hc

end
end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.EightAmbient
