module
public import Theory.Representation.Triality.RestrictedWeights.ConcreteFinitePeriodSource
public import Theory.Representation.TensorInvolutionDisplacement
/-!
# Inner triality displacement on the original finite action

The actual tensor classification and character-period theorem reduce the
original faithful irreducible module to its concrete basic factors. Taking
the gcd of a coefficient period and 3n gives the exact multiplier needed by
the root-operator bound. An actual nonidentity involution rules out the all-zero
word. The displacement estimate retains the original action and involution;
only algebraic universality and its character-field period remain explicit.
Source: Guralnick--Malle II, Lemma 8.6; GLS3 2.8.6 and 2.8.8.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
open Representation.BinaryOffender.NaturalTensor
namespace Triality.RestrictedWeights.Concrete
open Triality.SimplyConnected Triality.Standard
open SteinbergTensors SteinbergTensors.AlgebraicTensor
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]
variable (hu : IsUniversalVersion (groupVariety k))

theorem basic_zero_finrank : Module.finrank k ((basicFamily k hu).factor zeroWeight).Space = 1 := by
  obtain ⟨v,hv⟩ := (basicFamily k hu).highest zeroWeight
  apply RestrictedStep.finrank_eq_one_of_zero_highWeight (algebraicGeometry k hu)
    ((basicFamily k hu).factor zeroWeight).action ((basicFamily k hu).factor zeroWeight).irreducible v
  change HasHighWeight _ (algebraicGeometry k hu).borel (algebraicGeometry k hu).torus v
    ((algebraicGeometry k hu).leftWeightEmbedding (coefficient zeroWeight)) at hv
  have hz : coefficient zeroWeight = 0 := by ext i; rfl
  simpa only [hz, D4Geometry.leftWeightEmbedding_eq_raw, neg_zero] using hv

theorem native_tensor_nonzero_weight (n : ℕ) (hn : 0<n) (w : ℕ → BasicWeight)
    (t : BinaryCarrier n hn) (ht : orderOf t=2)
    (hf : Function.Injective (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) w n).ρ) :
    ∃ i,w i≠zeroWeight := by
  by_contra! hz
  let ρ := (tensor (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) w n).ρ
  have hd : Module.finrank k (tensor (basicFamily k hu).factor
      (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) w n) = 1 := by
    calc
      _ = ∏ i ∈ Finset.range n, Module.finrank k ((basicFamily k hu).factor (w i)).Space :=
        finrank_tensor _ (pointEnd (finiteGeometry k hu).frobenius) _ _ _
      _ = 1 := ?_
    apply Finset.prod_eq_one
    intro i _
    rw [hz, basic_zero_finrank]
  have ht2 : ρ t * ρ t=1 := by
    rw [←map_mul,←pow_two,←ht, pow_orderOf_eq_one, map_one]
  have hr := Representation.TensorInvolutionDisplacement.twice_displacement_le (ρ t) ht2
  rw [hd] at hr
  have hr0 : operatorFixedCodim (ρ t)=0 := by omega
  have he : ρ t=1 := by
    apply sub_eq_zero.mp
    apply LinearMap.range_eq_bot.mp
    exact Submodule.finrank_eq_zero.mp hr0
  have ht1 : t=1 := hf (he.trans (map_one ρ).symm)
  simp [ht1] at ht

private theorem periodic_gcd {α : Type*} {a : ℕ → α} {m n : ℕ}
    (hm : Function.Periodic a m) (hn : Function.Periodic a n) :
    Function.Periodic a (Nat.gcd m n) := by
  let shift : (ℕ → α) → (ℕ → α) := fun b i => b (i + 1)
  have hit (k : ℕ) (b : ℕ → α) (i : ℕ) : shift^[k] b i = b (i + k) := by
    induction k generalizing b i with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change shift^[k] b (i + 1) = b (i + (k + 1))
      rw [ih]
      congr 1
      omega
  have hp (k : ℕ) : Function.IsPeriodicPt shift k a ↔ Function.Periodic a k := by
    change shift^[k] a = a ↔ _
    simp only [funext_iff, hit, Function.Periodic]
  exact (hp _).mp (((hp m).mpr hm).gcd ((hp n).mpr hn))

include hu in
theorem native_faithful_character_displacement (n : ℕ) (hn : 0<n)
    (V : FDRep k (BinaryCarrier n hn)) (hi : Representation.IsIrreducible V.ρ)
    (hf : Function.Injective V.ρ) (d : ℕ) (hd : 0<d)
    (hchar : ∀ g, Representation.character V.ρ g ^ (2^d) = Representation.character V.ρ g)
    (t : BinaryCarrier n hn) (ht : orderOf t=2) :
    5*n < d * operatorFixedCodim (V.ρ t) := by
  obtain ⟨a,⟨e⟩,_⟩ := native_tensor_exhaustive k hu n hn V hi
  let R := tensor (basicFamily k hu).factor
    (finiteGeometry k hu).frobenius.onPoints (nativePointHom k n hn) (extendWeights hn a) n
  have hR : Function.Injective R.ρ := by
    intro x y hxy
    apply hf
    apply e.conj.injective
    simpa only [Representation.Equiv.conj_apply_self] using hxy
  have hp : Function.Periodic (extendWeights hn a) d := by
    apply (native_tensor_character_period k hu n hn a d).mp
    intro g
    rw [←Representation.char_iso e]
    exact hchar g
  have hpg := periodic_gcd hp (extendWeights_period_three hn a)
  have hs : 0<Nat.gcd d (3*n) := Nat.gcd_pos_of_pos_left _ hd
  have hb := native_tensor_involution_displacement k hu n hn (extendWeights hn a)
    (Nat.gcd d (3*n)) hs (Nat.gcd_dvd_right d (3*n)) (extendWeights_wrap hn a) hpg
    (native_tensor_nonzero_weight k hu n hn (extendWeights hn a) t ht hR) t ht
  have hr := operatorFixedCodim_eq_of_equiv (V.ρ t) (R.ρ t) e.toLinearEquiv
    (fun v => LinearMap.congr_fun (e.isIntertwining' t) v)
  rw [←hr] at hb
  exact hb.trans_le (Nat.mul_le_mul_right _ (Nat.le_of_dvd hd (Nat.gcd_dvd_left d (3*n))))
end Triality.RestrictedWeights.Concrete
