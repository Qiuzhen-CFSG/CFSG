module
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTrialityWeights
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.CubicSourceExclusionsTriality

/-!
# The short-root bound on the literal triality tensor

The four- and eleven-pair bounds give 11/24 of the artificial product of
basic dimensions. The exact twisted character period supplies 24r, giving
short-root displacement at least 11r on every faithful irreducible binary
module. This exceeds the 10r permitted for a source actor.
Source: Guralnick--Malle II, Lemma 8.6; Aschbacher--Smith K.3, p.457.
-/

public noncomputable section
open Theory.AlgebraicGroup
open Module Representation.BinaryOffender.NaturalTensor Representation.TensorInvolutionDisplacement
open Triality.RestrictedWeights.SteinbergTensors
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Triality.RestrictedWeights Triality.RestrictedWeights.Concrete
open Triality.RestrictedWeights.BasicDisplacement
open Triality.Standard Triality.SimplyConnected
open Triality.InnerDisplacement
namespace CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
universe u v
variable {k : Type u} [Field k] [CharP k 2]
variable {G : Type v} [Group G]
private theorem tensorPrefix_short_weighted (V : ℕ → FDRep k G)
    (t : G) (ht : t^2=1) (d : ℕ→ℕ)
    (hd : ∀ i, 0<d i) (hdim : ∀ i, d i ≤ finrank k (V i))
    (hrank : ∀ i, 1<d i → 11*d i ≤ 24*operatorFixedCodim ((V i).ρ t))
    (n : ℕ) (hne : ∃ i<n, 1<d i) :
    11*(∏ i ∈ Finset.range n, d i) ≤ 24*operatorFixedCodim ((tensorPrefix V n).ρ t) := by
  induction n with
  | zero => obtain ⟨i,hi,_⟩ := hne; omega
  | succ n ih =>
    have hl := mul_finrank_le_tprod_displacement_left (tensorPrefix V n).ρ (V n).ρ t ht
    have hr := mul_finrank_le_tprod_displacement_right (tensorPrefix V n).ρ (V n).ρ t ht
    change 11*(∏ i ∈ Finset.range (n+1),d i) ≤
      24*operatorFixedCodim (Representation.tprod (tensorPrefix V n).ρ (V n).ρ t)
    rw [Finset.prod_range_succ]
    by_cases hold : ∃ i<n,1<d i
    · calc
        11*((∏ i ∈ Finset.range n,d i)*d n) =
            (11*(∏ i ∈ Finset.range n,d i))*d n := by ring
        _ ≤
            (24*operatorFixedCodim ((tensorPrefix V n).ρ t))*finrank k (V n) :=
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
      exact (hrank n hn).trans (Nat.mul_le_mul_left 24
        ((Nat.le_mul_of_pos_left _ hp).trans hr))

private theorem eleven_mul_le_tensor_displacement (V : ℕ → FDRep k G)
    (t : G) (ht : t^2=1) (w : ℕ→BasicWeight) (n s : ℕ)
    (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight)
    (hdim : ∀ i,minimumDegree (w i)≤finrank k (V i))
    (hrank : ∀ i,w i≠zeroWeight →
      4≤operatorFixedCodim ((V i).ρ t) ∧
      (diagramAction (w i)=w i → 11≤operatorFixedCodim ((V i).ρ t))) :
    11*n ≤ s*operatorFixedCodim ((tensorPrefix V n).ρ t) := by
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
  have hprod := Triality.BinaryDegree.twenty_four_mul_le_twisted_product hn hs hsn hwrap
    minimumDegree_diagram hp (fun i=>minimumDegree_pos (w i)) hlarge
    (fun i=>minimumDegree_fixed (w i))
  have hr := tensorPrefix_short_weighted V t ht (fun i=>minimumDegree (w i))
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

private theorem eleven_mul_le_fixed_tensor_displacement [IsAlgClosed k]
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
      4≤operatorFixedCodim (((A a).action.action (ι t)).val) ∧
      (diagramAction a=a → 11≤operatorFixedCodim (((A a).action.action (ι t)).val))) :
    11*n ≤ s*operatorFixedCodim ((tensor A φ ι w n).ρ t) := by
  have hiter : ∀ i : ℕ,(φ^i) (ι t)=ι t := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ]
      change (φ^i) (φ (ι t)) = ι t
      rw [hφ,ih]
  apply eleven_mul_le_tensor_displacement (fun i=>twistedFactor A φ ι (w i) i)
    t ht w n s hn hs hsn hwrap hp hne
  · intro i
    exact hdim (w i)
  · intro i hi
    change 4≤operatorFixedCodim (((A (w i)).action.action ((φ^i) (ι t))).val) ∧
      (diagramAction (w i)=w i →
        11≤operatorFixedCodim (((A (w i)).action.action ((φ^i) (ι t))).val))
    rw [hiter]
    exact hrank (w i) hi
private theorem eleven_mul_le_short_root_tensor_displacement
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
    (hu : IsUniversalVersion (groupVariety k))
    {G : Type v} [Group G] (ι : G →* Variety.Point (groupVariety k))
    (t : G) (ht : t^2=1) (hmark : ι t = rootOperator k true)
    (w : ℕ → BasicWeight) (n s : ℕ) (hn : 0<n) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight) :
    11*n ≤ s*operatorFixedCodim ((tensor (Concrete.basicFamily k hu).factor
      (Concrete.finiteGeometry k hu).frobenius.onPoints ι w n).ρ t) := by
  have hφ : (Concrete.finiteGeometry k hu).frobenius.onPoints (ι t)=ι t := by
    rw [hmark]
    change (regularFrobeniusLift k 1).onPoints (rootOperator k true) = _
    simp only [rootOperator,↓reduceIte,map_mul,
        regularFrobeniusLift_onPoints,GraphField.frobenius_rootPoint,one_pow]
  apply eleven_mul_le_fixed_tensor_displacement (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints ι t ht hφ
    w n s hn hs hsn hwrap hp hne (minimumDegree_le_basic_finrank k hu)
  intro a ha
  rw [hmark]
  exact TrialityWeights.basic_short_displacement k hu a ha

theorem triality_tensor_short_bound
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
    (hu : IsUniversalVersion (groupVariety k)) (n : ℕ) (hn : 0<n)
    (w : ℕ → BasicWeight) (s : ℕ) (hs : 0<s) (hsn : s ∣ 3*n)
    (hwrap : ∀ i,w (i+n)=diagramAction (w i)) (hp : Function.Periodic w s)
    (hne : ∃ i,w i≠zeroWeight) (t : BinaryCarrier n hn)
    (ht : EvenInvolutionGeometry.IsShortRootInvolution n hn t) :
    11*n ≤ s * operatorFixedCodim ((tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) w n).ρ t) := by
  let ρ := (tensor (basicFamily k hu).factor (finiteGeometry k hu).frobenius.onPoints
    (nativePointHom k n hn) w n).ρ
  obtain ⟨a,ha,hc⟩ := ht
  have hc' := (EvenInvolutionGeometry.shortRoot_conjugate_one n hn a ha).trans hc
  have hb := eleven_mul_le_short_root_tensor_displacement k hu (nativePointHom k n hn)
    (EvenInvolutionGeometry.shortRoot n hn 1) (EvenInvolutionGeometry.shortRoot_sq n hn 1)
    (nativePointHom_rootOne k n hn true) w n s hn hs hsn hwrap hp hne
  obtain ⟨g,hg⟩ := isConj_iff.mp hc'
  have hrank : operatorFixedCodim (ρ (EvenInvolutionGeometry.shortRoot n hn 1)) =
      operatorFixedCodim (ρ t) := by
    apply operatorFixedCodim_eq_of_equiv _ _
      (LinearMap.GeneralLinearGroup.toLinearEquiv (Representation.asGroupHom ρ g))
    intro v
    change ρ g (ρ (EvenInvolutionGeometry.shortRoot n hn 1) v) = ρ t (ρ g v)
    have hh : g * EvenInvolutionGeometry.shortRoot n hn 1 = t * g := by rw [←hg]; group
    change ((ρ g * ρ (EvenInvolutionGeometry.shortRoot n hn 1)) : Module.End k _) v =
      ((ρ t * ρ g) : Module.End k _) v
    rw [←map_mul,←map_mul,hh]
  exact hb.trans_eq (congrArg (fun d => s*d) hrank)
end CFSG.Quasithin.ChapterK.Exceptional.CubicSourceExclusions
