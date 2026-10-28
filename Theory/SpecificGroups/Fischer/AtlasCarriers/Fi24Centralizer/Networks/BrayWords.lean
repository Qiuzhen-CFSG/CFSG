module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi24Centralizer.Networks.Transport
public import Theory.GroupAction.PackedPermutation.Words
/-!
# Certified network words for the two Bray products

Concatenation and reversal express the literal words in the original two
Fi24 generators. The fifth-power checks are separate finite certificates;
this module transports their conclusion to the original ATLAS subgroup.
-/
@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks
open Theory.GroupAction.PackedPermutation

private lemma valid_append {ss ts : List Stage}
    (hs : ∀ s∈ss, s.Valid 19 524288) (ht : ∀ s∈ts, s.Valid 19 524288) :
    ∀ s∈ss++ts, s.Valid 19 524288 := by
  intro s h
  rcases List.mem_append.mp h with h | h
  · exact hs s h
  · exact ht s h

private lemma valid_reverse {ss : List Stage} (h : ∀ s∈ss, s.Valid 19 524288) :
    ∀ s∈ss.reverse, s.Valid 19 524288 := fun s hs => h s (List.mem_reverse.mp hs)

noncomputable def netG0 : List Stage :=
  networkA ++ networkB ++ networkA ++ networkB ++ networkB ++
  networkA ++ networkB ++ networkB ++ networkA ++ networkB
noncomputable def netG1 : List Stage :=
  networkA ++ networkB ++ networkB ++ networkA ++ networkB ++
  networkA ++ networkB ++ networkB

 theorem netG0_valid : ∀ s∈netG0, s.Valid 19 524288 := by
  unfold netG0
  repeat' first | exact networkA_valid | exact networkB_valid | apply valid_append
 theorem netG1_valid : ∀ s∈netG1, s.Valid 19 524288 := by
  unfold netG1
  repeat' first | exact networkA_valid | exact networkB_valid | apply valid_append

noncomputable def netK0 : List Stage := networkA ++ (netG0.reverse ++ networkA ++ netG0)
noncomputable def netK1 : List Stage := networkA ++ (netG1.reverse ++ networkA ++ netG1)

theorem netK0_valid : ∀ s∈netK0, s.Valid 19 524288 :=
  valid_append networkA_valid (valid_append (valid_append (valid_reverse netG0_valid)
    networkA_valid) netG0_valid)
theorem netK1_valid : ∀ s∈netK1, s.Valid 19 524288 :=
  valid_append networkA_valid (valid_append (valid_append (valid_reverse netG1_valid)
    networkA_valid) netG1_valid)

noncomputable def permG0 := permutation 19 524288 netG0 netG0_valid
noncomputable def permG1 := permutation 19 524288 netG1 netG1_valid
noncomputable def permK0 := permutation 19 524288 netK0 netK0_valid
noncomputable def permK1 := permutation 19 524288 netK1 netK1_valid

theorem permG0_eq : permG0 = permA*permB*permA*permB^2*permA*permB^2*permA*permB := by
  simp only [permG0, netG0, permutation_append, permA, permB, pow_two, mul_assoc]
theorem permG1_eq : permG1 = permA*permB^2*permA*permB*permA*permB^2 := by
  simp only [permG1, netG1, permutation_append, permA, permB, pow_two, mul_assoc]
theorem permK0_eq : permK0 = permA*(permG0⁻¹*permA*permG0) := by
  simp only [permK0, netK0, permutation_append, permA, permG0]
  rw [permutation_reverse 19 524288 netG0 netG0_valid]
theorem permK1_eq : permK1 = permA*(permG1⁻¹*permA*permG1) := by
  simp only [permK1, netK1, permutation_append, permA, permG1]
  rw [permutation_reverse 19 524288 netG1 netG1_valid]

theorem g0_intertwines : Intertwines g0 permG0 := by
  rw [permG0_eq]
  exact (((((((a_intertwines.mul b_intertwines).mul a_intertwines).mul
    (b_intertwines.pow 2)).mul a_intertwines).mul (b_intertwines.pow 2)).mul
    a_intertwines).mul b_intertwines)
theorem g1_intertwines : Intertwines g1 permG1 := by
  rw [permG1_eq]
  exact ((((a_intertwines.mul (b_intertwines.pow 2)).mul a_intertwines).mul
    b_intertwines).mul a_intertwines).mul (b_intertwines.pow 2)
theorem k0_intertwines : Intertwines k0 permK0 := by
  rw [permK0_eq]
  exact a_intertwines.mul ((g0_intertwines.inv.mul a_intertwines).mul g0_intertwines)
theorem k1_intertwines : Intertwines k1 permK1 := by
  rw [permK1_eq]
  exact a_intertwines.mul ((g1_intertwines.inv.mul a_intertwines).mul g1_intertwines)
end Sporadic.Fischer.Fi24Prime.CentralizerSection.Networks
