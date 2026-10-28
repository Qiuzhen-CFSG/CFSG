module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.TwoGroup
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.BinarySpan

/-!
# Binary normal forms modulo the distinguished involution

The certified max2 relations make the images of the thirteen generators
commuting involutions after quotienting by the central involution. The existing
binary-span theorem therefore gives a binary product differing from any element
of the relative normal closure by a central power. A product's commutator with
a fixed element is the Boolean pairing of its coordinates with the generator
commutators.

This is the normal-form step for the intrinsic-center bound motivated by GLS3,
Table 5.3i, printed p.270. All quotients and subgroups are inside `localSubgroup`.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.IntrinsicCenter
open Janko4.Cardinality.KernelCount

/-- Every element of the relative normal closure has binary coordinates modulo the involution. -/
lemma exists_binary_mod_center (g : localSubgroup) (hg : g ∈ localNormalClosure) :
    ∃ v, (binaryProduct basis v)⁻¹ * g ∈ Subgroup.zpowers subgroupInvolution := by
  let Z := Subgroup.zpowers subgroupInvolution
  have hz : Z ≤ Subgroup.center localSubgroup := Subgroup.zpowers_le.mpr involution_mem_center
  let : Z.Normal := ⟨fun n hn x => by
    rw [(Subgroup.mem_center_iff.mp (hz hn)) x, mul_inv_cancel_right]
    exact hn⟩
  let q := QuotientGroup.mk' Z
  have hqt : q subgroupInvolution = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
  have hqs : ∀ i, q (basis i) * q (basis i) = 1 := by
    intro i
    rw [← map_mul, ← pow_two]
    rcases basis_square i with hi | hi <;> rw [hi]
    · exact map_one q
    · exact hqt
  have hqc : ∀ i j, Commute (q (basis i)) (q (basis j)) := by
    intro i j
    change q (basis i) * q (basis j) = q (basis j) * q (basis i)
    rw [← map_mul, ← map_mul]
    rcases basis_commutator i j with hij | hij
    · rw [hij]
    · rw [hij, map_mul, hqt, mul_one]
  have hqg : q g ∈ Subgroup.closure (Set.range (fun i => q (basis i))) := by
    have hm : span ≤ (Subgroup.closure (Set.range (fun i => q (basis i)))).comap q := by
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨i, rfl⟩
      exact Subgroup.subset_closure (Set.mem_range_self i)
    exact hm (localNormalClosure_eq_span ▸ hg)
  obtain ⟨v, hv⟩ := (mem_closure_iff_binaryProduct _ hqs hqc (q g)).mp hqg
  refine ⟨v, (QuotientGroup.eq_one_iff _).mp ?_⟩
  change q ((binaryProduct basis v)⁻¹ * g) = 1
  rw [map_mul, map_inv, map_binaryProduct, hv, inv_mul_cancel]

/-- Evaluate a Boolean exponent at a group element. -/
def bit {G : Type*} [One G] (t : G) (b : Bool) : G := if b then t else 1
private lemma bit_xor {G : Type*} [Group G] (t : G) (ht : t ^ 2 = 1) (a b : Bool) :
    bit t (a ^^ b) = bit t a * bit t b := by
  cases a <;> cases b <;> simp [bit, ← pow_two, ht]
/-- The binary dot product, expressed as a finite XOR. -/
def pairing {n : ℕ} (v w : Fin n → Bool) : Bool :=
  (List.ofFn (fun i => v i && w i)).foldr Bool.xor false
private lemma pairing_succ {n : ℕ} (v w : Fin (n + 1) → Bool) :
    pairing v w = ((v 0 && w 0) ^^ pairing (fun i => v i.succ) (fun i => w i.succ)) := by
  simp [pairing, List.ofFn_succ]

private lemma twisted_mul {G : Type*} [Group G] (a b g s r : G)
    (ha : a * g = g * a * s) (hb : b * g = g * b * r) (hs : Commute s b) :
    (a * b) * g = g * (a * b) * (s * r) := by
  calc
    (a * b) * g = a * (b * g) := mul_assoc _ _ _
    _ = a * (g * b * r) := by rw [hb]
    _ = (a * g) * b * r := by simp only [mul_assoc]
    _ = (g * a * s) * b * r := by rw [ha]
    _ = g * (a * b) * (s * r) := by rw [mul_assoc (g * a) s b, hs.eq]; simp only [mul_assoc]

/-- Central generator commutators multiply according to the binary dot product. -/
lemma binaryProduct_twist {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (v w : Fin n → Bool) (g t : G)
    (ht : t ∈ Subgroup.center G) (ht2 : t ^ 2 = 1)
    (he : ∀ i, e i * g = g * e i * bit t (w i)) :
    binaryProduct e v * g = g * binaryProduct e v * bit t (pairing v w) := by
  induction n with
  | zero => simp [binaryProduct, pairing, bit]
  | succ n ih =>
    rw [binaryProduct_succ, pairing_succ, bit_xor t ht2]
    apply twisted_mul
    · cases v 0 <;> simp [bit, he]
    · exact ih _ _ _ (fun i => he i.succ)
    · unfold bit
      split_ifs
      · exact ((Subgroup.mem_center_iff.mp ht) _).symm
      · exact Commute.one_left _
end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl.IntrinsicCenter
