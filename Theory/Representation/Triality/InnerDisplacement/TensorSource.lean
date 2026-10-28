module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Construction
public import Theory.Representation.Triality.BinaryDegree.TwistedProduct
public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.TensorRank.Linear

/-!
# Inner triality displacement from actual tensor factors

Tensoring an involution multiplies its displacement by at least the dimension
of the other factor. Use artificial lower degrees 1, 8 and 24 for the zero,
nonzero and nonzero diagram-fixed D4 weights. Basic operator ranks 2 and 6
therefore give at least one quarter of the corresponding product. The proved
threefold twisted-period arithmetic gives the strict binary bound 5n.

The fixed-point consumer keeps the literal Frobenius-twisted representations.
It assumes the independent basic operator bounds and tensor character period;
it does not infer displacement from whole-module dimension or assert finite
representation realization. Those are separate source producers.
Source: GLS3 §2.8 and Guralnick--Malle, Classification of 2F-modules II, 8.6.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Module Representation.BinaryOffender.NaturalTensor Representation.TensorInvolutionDisplacement
open Triality.RestrictedWeights.SteinbergTensors
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.InnerDisplacement
universe u v
variable {k : Type u} [Field k] [CharP k 2]
variable {G : Type v} [Group G]

/-- An actual involutory tensor has at least a quarter of the product of
lower dimension bounds, once a nontrivial factor supplies the same rank bound. -/
theorem tensorPrefix_displacement_weighted (V : ℕ → FDRep k G)
    (t : G) (ht : t^2=1) (d : ℕ→ℕ)
    (hd : ∀ i, 0<d i) (hdim : ∀ i, d i ≤ finrank k (V i))
    (hrank : ∀ i, 1<d i → d i ≤ 4*operatorFixedCodim ((V i).ρ t))
    (n : ℕ) (hne : ∃ i<n, 1<d i) :
    (∏ i ∈ Finset.range n, d i) ≤ 4*operatorFixedCodim ((tensorPrefix V n).ρ t) := by
  induction n with
  | zero => obtain ⟨i,hi,_⟩ := hne; omega
  | succ n ih =>
    have hl := mul_finrank_le_tprod_displacement_left (tensorPrefix V n).ρ (V n).ρ t ht
    have hr := mul_finrank_le_tprod_displacement_right (tensorPrefix V n).ρ (V n).ρ t ht
    change (∏ i ∈ Finset.range (n+1),d i) ≤
      4*operatorFixedCodim (Representation.tprod (tensorPrefix V n).ρ (V n).ρ t)
    rw [Finset.prod_range_succ]
    by_cases hold : ∃ i<n,1<d i
    · calc
        (∏ i ∈ Finset.range n,d i)*d n ≤
            (4*operatorFixedCodim ((tensorPrefix V n).ρ t))*finrank k (V n) :=
          Nat.mul_le_mul (ih hold) (hdim n)
        _ ≤ _ := by nlinarith
    · have hone : ∏ i ∈ Finset.range n,d i = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hn := hd i
        have hi' := Finset.mem_range.mp hi
        have hnot : ¬1<d i := fun h => hold ⟨i,hi',h⟩
        omega
      have hn : 1<d n := by obtain ⟨i,hi,hdi⟩ := hne; by_cases e:i=n; simpa[e] using hdi; exact (hold ⟨i,by omega,hdi⟩).elim
      have hp : 0<finrank k (tensorPrefix V n) := by
        rw [finrank_tensorPrefix]
        exact Finset.prod_pos (fun i _ => (hd i).trans_le (hdim i))
      rw [hone,one_mul]
      exact (hrank n hn).trans (Nat.mul_le_mul_left 4
        ((Nat.le_mul_of_pos_left _ hp).trans hr))

/-- Numerical weights sufficient for the displacement calculation. -/
@[expose] def minimumDegree (a : BasicWeight) : ℕ :=
  if a=zeroWeight then 1 else if diagramAction a=a then 24 else 8

theorem minimumDegree_pos : ∀ a, 0<minimumDegree a := by decide

theorem minimumDegree_diagram : ∀ a, minimumDegree (diagramAction a)=minimumDegree a := by decide

theorem minimumDegree_nonzero : ∀ a, a≠zeroWeight → 8≤minimumDegree a := by decide

theorem minimumDegree_fixed : ∀ a, diagramAction a=a → 8≤minimumDegree a → 24≤minimumDegree a := by decide

/-- The actual coefficient-field multiplier turns the weak basic operator
bounds into the strict inner triality bound. The finite tensor realization
and its exact diagram-twisted character period remain separate source inputs. -/
theorem five_mul_lt_tensor_displacement (V : ℕ → FDRep k G)
    (t : G) (ht : t^2=1) (w : ℕ→BasicWeight) (n s : ℕ)
    (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight)
    (hdim : ∀ i,minimumDegree (w i)≤finrank k (V i))
    (hrank : ∀ i,w i≠zeroWeight →
      2≤operatorFixedCodim ((V i).ρ t) ∧
      (diagramAction (w i)=w i → 6≤operatorFixedCodim ((V i).ρ t))) :
    5*n < s*operatorFixedCodim ((tensorPrefix V n).ρ t) := by
  have hw : Function.Periodic (fun i=>minimumDegree (w i)) n :=
    fun i => by
      change minimumDegree (w (i+n)) = minimumDegree (w i)
      rw [hwrap,minimumDegree_diagram]
  obtain ⟨i,hi⟩ := hne
  have hni : ∃ j<n,1<minimumDegree (w j) := by
    refine ⟨i%n,Nat.mod_lt i hn,?_⟩
    rw [hw.map_mod_nat]
    exact lt_of_lt_of_le (by decide:1<8) (minimumDegree_nonzero _ hi)
  have hlarge : ∃ i,8≤minimumDegree (w i) := ⟨i,minimumDegree_nonzero _ hi⟩
  have hprod := BinaryDegree.twenty_four_mul_le_twisted_product hn hs hsn hwrap
    minimumDegree_diagram hp (fun i=>minimumDegree_pos (w i)) hlarge
    (fun i=>minimumDegree_fixed (w i))
  have hr := tensorPrefix_displacement_weighted V t ht (fun i=>minimumDegree (w i))
    (fun i=>minimumDegree_pos (w i)) hdim (fun i hd=>?_) n hni
  · nlinarith [Nat.mul_le_mul_left s hr]
  · have hnon : w i≠zeroWeight := by intro he; simp [minimumDegree,he] at hd
    have hi := hrank i hnon
    by_cases hf : diagramAction (w i)=w i
    · have hh := hi.2 hf
      simp only [minimumDegree,if_neg hnon,if_pos hf]
      omega
    · simp only [minimumDegree,if_neg hnon,if_neg hf]
      omega

/-- Literal application to the restricted Frobenius tensor. A fixed group
point has the same operator in every twisted basic factor. -/
theorem five_mul_lt_fixed_tensor_displacement [IsAlgClosed k]
    {K : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup K]
    (A : BasicWeight → RationalFactor K)
    (φ : Monoid.End (Theory.AlgebraicGroup.Variety.Point K))
    (ι : G →* Theory.AlgebraicGroup.Variety.Point K)
    (t : G) (ht : t^2=1) (hφ : φ (ι t) = ι t)
    (w : ℕ→BasicWeight) (n s : ℕ) (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight)
    (hdim : ∀ a,minimumDegree a≤finrank k (A a).Space)
    (hrank : ∀ a,a≠zeroWeight →
      2≤operatorFixedCodim (((A a).action.action (ι t)).val) ∧
      (diagramAction a=a → 6≤operatorFixedCodim (((A a).action.action (ι t)).val))) :
    5*n < s*operatorFixedCodim ((tensor A φ ι w n).ρ t) := by
  have hiter : ∀ i : ℕ,(φ^i) (ι t)=ι t := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ]
      change (φ^i) (φ (ι t)) = ι t
      rw [hφ,ih]
  apply five_mul_lt_tensor_displacement (fun i=>twistedFactor A φ ι (w i) i)
    t ht w n s hn hs hsn hwrap hp hne
  · intro i
    exact hdim (w i)
  · intro i hi
    change 2≤operatorFixedCodim (((A (w i)).action.action ((φ^i) (ι t))).val) ∧
      (diagramAction (w i)=w i →
        6≤operatorFixedCodim (((A (w i)).action.action ((φ^i) (ι t))).val))
    rw [hiter]
    exact hrank (w i) hi
end Triality.InnerDisplacement
