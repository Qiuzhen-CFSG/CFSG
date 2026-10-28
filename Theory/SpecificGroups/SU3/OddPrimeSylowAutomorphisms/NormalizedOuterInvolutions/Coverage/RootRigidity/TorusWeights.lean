module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.Roots

public import Mathlib.Data.Nat.Prime.Basic

/-!
# The torus weights span the quadratic field additively

The first-coordinate weight is `k / conj(k)^2`, in the convention of the
existing Hermitian torus matrices. Its kernel consists of cube roots of unity,
so has order at most three. For a field of order `p²`, with `p ≥ 3`, its image
is too large to lie in a proper additive subgroup: such a subgroup has order
at most `p`, and also contains zero, which is absent from the weight image.

This proves Steinberg, Theorem 36, step (3), and the multiplicativity inference
in step (4), `refs/KGroup/GLS3/Chapter2St1.tex`. No torus lift through the
projective scalar kernel is assumed, and the argument includes `p = 3`.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] (J : HermitianForm 3 E)

@[expose] public def torusWeight : Eˣ →* Eˣ where
  toFun k := k * ((Units.map J.conj.toMonoidHom) k)⁻¹ ^ 2
  map_one' := by simp
  map_mul' x y := by simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]

public theorem torusWeight_val (k : Eˣ) :
    (torusWeight J k : E) = (k : E) / (J.conj (k : E)) ^ 2 := by
  simp [torusWeight, div_eq_mul_inv]

private theorem torusWeight_ker_cube (k : Eˣ) (hk : k ∈ (torusWeight J).ker) : k ^ 3 = 1 := by
  have hv := congrArg (fun u : Eˣ => (u : E)) (MonoidHom.mem_ker.mp hk)
  rw [torusWeight_val] at hv
  have hbar : J.conj (k : E) ≠ 0 := (map_ne_zero J.conj).mpr (Units.ne_zero k)
  have he : (k : E) = J.conj (k : E) ^ 2 := (div_eq_one_iff_eq (pow_ne_zero 2 hbar)).mp hv
  have hf := congrArg J.conj he
  rw [map_pow, J.conj_involutive] at hf
  have hh : (k : E) ^ 4 = (k : E) := by
    calc
      (k : E) ^ 4 = ((k : E) ^ 2) ^ 2 := by ring
      _ = J.conj (k : E) ^ 2 := by rw [← hf]
      _ = (k : E) := he.symm
  apply Units.ext
  change (k : E) ^ 3 = 1
  apply mul_left_cancel₀ (Units.ne_zero k)
  calc
    (k : E) * (k : E) ^ 3 = (k : E) ^ 4 := by ring
    _ = (k : E) := hh
    _ = (k : E) * 1 := (mul_one _).symm

private theorem torusWeight_ker_card [Finite E] : Nat.card (torusWeight J).ker ≤ 3 := by
  have hle : (torusWeight J).ker ≤ (powMonoidHom 3 : Eˣ →* Eˣ).ker := by
    intro k hk
    exact torusWeight_ker_cube J k hk
  have hh := (Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)).trans_eq (IsCyclic.card_powMonoidHom_ker (G := Eˣ) 3)
  exact hh.trans (Nat.gcd_le_right _ (by decide))

/-- The cubic kernel bound is valid over every finite coefficient field,
independently of the prime-order hypothesis used in the span proof below. -/
public theorem torusWeight_kernel_card_le_three [Finite E] :
    Nat.card (torusWeight J).ker ≤ 3 := by
  exact torusWeight_ker_card J

public theorem torusWeight_additive_span [Finite E] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hcard : Nat.card E = p ^ 2) :
    AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E))) = ⊤ := by
  classical
  let S := AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E)))
  have hsmall (hne : S ≠ ⊤) : Nat.card S ≤ p := by
    have hd : Nat.card S ∣ p ^ 2 := hcard ▸ AddSubgroup.card_addSubgroup_dvd_card S
    obtain ⟨n, hn, hc⟩ := (Nat.dvd_prime_pow hp).mp hd
    have hn2 : n ≠ 2 := by
      intro hn2
      apply hne
      exact S.eq_top_of_card_eq (by simpa [hn2, hcard] using hc)
    have hn1 : n = 0 ∨ n = 1 := by omega
    rcases hn1 with rfl | rfl
    · simpa using hc.le.trans hp.one_le
    · simpa using hc.le
  let e : (torusWeight J).range → S := fun x =>
    ⟨(x.val : E), AddSubgroup.subset_closure (by
      obtain ⟨k, hk⟩ := x.property
      exact ⟨k, congrArg (fun u : Eˣ => (u : E)) hk⟩)⟩
  have heinj : Function.Injective e := by
    intro x y he
    apply Subtype.ext
    exact Units.ext (congrArg Subtype.val he)
  have henot : ¬ Function.Surjective e := by
    intro he
    obtain ⟨x, hx⟩ := he 0
    exact Units.ne_zero x.val (congrArg Subtype.val hx)
  have hrlt : Nat.card (torusWeight J).range < Nat.card S := by
    let := Fintype.ofFinite (torusWeight J).range
    let := Fintype.ofFinite S
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective e heinj henot
  have hprod := (torusWeight J).ker.card_mul_index
  rw [Subgroup.index_ker, Nat.card_units, hcard] at hprod
  have hk := torusWeight_ker_card J
  by_contra hne
  have hs := hsmall hne
  have hle : p ^ 2 - 1 ≤ 3 * (p - 1) := by
    rw [← hprod]
    exact Nat.mul_le_mul hk (by omega)
  have hp2 : 1 ≤ p ^ 2 := one_le_pow₀ hp.one_le
  have hp1 : 1 ≤ p := hp.one_le
  have hx := Nat.sub_add_cancel hp2
  have hy := Nat.sub_add_cancel hp1
  nlinarith

private def multiplicativeLocus (f : E ≃+ E) : AddSubgroup E where
  carrier := {a | ∀ x, f (a * x) = f a * f x}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb x
    simp only [add_mul, map_add]
    rw [ha x, hb x]
  neg_mem' := by
    intro a ha x
    simp only [neg_mul, map_neg]
    rw [ha x]

public theorem mul_eq_of_torusWeight [Finite E] {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    (hcard : Nat.card E = p ^ 2) (f : E ≃+ E)
    (hweight : ∀ k : Eˣ, ∀ x : E, f ((torusWeight J k : E) * x) =
      f (torusWeight J k : E) * f x) (a x : E) : f (a * x) = f a * f x := by
  have hle : AddSubgroup.closure (Set.range (fun k : Eˣ => (torusWeight J k : E))) ≤
      multiplicativeLocus f := by
    apply (AddSubgroup.closure_le _).mpr
    rintro _ ⟨k, rfl⟩
    exact hweight k
  rw [torusWeight_additive_span J hp hp3 hcard] at hle
  exact hle (AddSubgroup.mem_top a) x

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
