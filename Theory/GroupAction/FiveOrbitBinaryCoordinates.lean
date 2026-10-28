module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# Binary coordinates from a five-orbit

For a fixed-point-free action of an order-five group on an elementary abelian
2-group of order sixteen, any four consecutive points of a nonidentity orbit
are a binary basis. The product of all five orbit points is fixed and hence
trivial. Thus the first four span the whole orbit. Their binary words form a
subgroup, and invariant simplicity makes the orbit generate the group.
Surjectivity between two sets of order sixteen gives uniqueness.

This is the elementary orbit calculation underlying Parrott, *A characterization
of the Tits' simple group* (1972), pp.672–674, and Thompson VI, p.630.
-/

namespace Theory.GroupAction
open Subgroup
open scoped IsMulCommutative

private def binaryWord4 {V : Type*} [Group V]
    (v : Fin 4 → V) (e : Fin 4 → Fin 2) : V :=
  v 0 ^ (e 0).val * v 1 ^ (e 1).val * v 2 ^ (e 2).val * v 3 ^ (e 3).val

private theorem binaryWord4_mul {V : Type*} [Group V] [IsMulCommutative V]
    (v : Fin 4 → V) (hv : ∀ i, v i * v i = 1) (e f : Fin 4 → Fin 2) :
    binaryWord4 v (e + f) = binaryWord4 v e * binaryWord4 v f := by
  have hp (i : Fin 4) (a b : Fin 2) :
      v i ^ (a + b).val = v i ^ a.val * v i ^ b.val := by
    fin_cases a <;> fin_cases b <;> simp [hv]
  simp only [binaryWord4, Pi.add_apply, hp]
  ac_rfl

private def binaryWord4Range {V : Type*} [Group V] [IsMulCommutative V]
    (v : Fin 4 → V) (hv : ∀ i, v i * v i = 1) : Subgroup V where
  carrier := Set.range (binaryWord4 v)
  one_mem' := ⟨0, by simp [binaryWord4]⟩
  mul_mem' := by
    rintro _ _ ⟨e, rfl⟩ ⟨f, rfl⟩
    exact ⟨e + f, binaryWord4_mul v hv e f⟩
  inv_mem' := by
    rintro _ ⟨e, rfl⟩
    refine ⟨e, ?_⟩
    apply (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← binaryWord4_mul v hv]
    have he : e + e = 0 := by
      funext i
      change e i + e i = 0
      generalize e i = a
      fin_cases a <;> rfl
    rw [he]
    simp [binaryWord4]

private theorem binaryWord4Range_mem {V : Type*} [Group V] [IsMulCommutative V]
    (v : Fin 4 → V) (hv : ∀ i, v i * v i = 1) (i : Fin 4) :
    v i ∈ binaryWord4Range v hv := by
  change ∃ e, binaryWord4 v e = v i
  fin_cases i
  · exact ⟨![1,0,0,0], by simp [binaryWord4]⟩
  · exact ⟨![0,1,0,0], by simp [binaryWord4]⟩
  · exact ⟨![0,0,1,0], by simp [binaryWord4]⟩
  · exact ⟨![0,0,0,1], by simp [binaryWord4]⟩

/-- Every nonidentity five-orbit on an elementary group of order sixteen
has its first four points as a binary basis. The fifth is their product. -/
public theorem five_orbit_binary_coordinates
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hA : Nat.card A = 5) (hV : Nat.card V = 16)
    (hfixed : FixedPoints.subgroup A V = ⊥)
    (b : V) (hb : b ≠ 1) (g : A) (hg : g ≠ 1) :
    (g ^ 4 • b = b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b)) ∧
    Function.Bijective (fun e : Fin 4 → Fin 2 =>
      (g ^ 0 • b) ^ (e 0).val * (g ^ 1 • b) ^ (e 1).val *
        (g ^ 2 • b) ^ (e 2).val * (g ^ 3 • b) ^ (e 3).val) := by
  change (g ^ 4 • b = b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b)) ∧
    Function.Bijective (binaryWord4 (fun i : Fin 4 => g ^ i.val • b))
  classical
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hgen : zpowers g = ⊤ := zpowers_eq_top_of_prime_card hA hg
  have hg5 : g ^ 5 = 1 := by simpa [hA] using (pow_card_eq_one' (x := g))
  have hsq (v : V) : v * v = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hs : g • (b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b) * (g ^ 4 • b)) =
      b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b) * (g ^ 4 • b) := by
    simp only [smul_mul', smul_smul, ← pow_succ', ← pow_two, hg5, one_smul]
    norm_num1
    ac_rfl
  have hsum : b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b) * (g ^ 4 • b) = 1 := by
    apply hfixed.le
    intro a
    have ha : a ∈ MulAction.stabilizer A
        (b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b) * (g ^ 4 • b)) := by
      apply (show zpowers g ≤ MulAction.stabilizer A _ from zpowers_le.mpr hs)
      rw [hgen]
      exact mem_top a
    exact ha
  have hrel : g ^ 4 • b = b * (g • b) * (g ^ 2 • b) * (g ^ 3 • b) := by
    have hinv (v : V) : v⁻¹ = v := inv_eq_of_mul_eq_one_left (hsq v)
    exact (eq_inv_of_mul_eq_one_right hsum).trans (hinv _)
  refine ⟨hrel, ?_⟩
  let v : Fin 4 → V := fun i => g ^ i.val • b
  let S := binaryWord4Range v (fun i => hsq (v i))
  have hvmem (i : Fin 4) : v i ∈ S := binaryWord4Range_mem v _ i
  have hmem (a : A) : a • b ∈ S := by
    have hord : orderOf g = 5 := orderOf_eq_prime hg5 hg
    obtain ⟨n, hnlt, hn⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp (show a ∈ zpowers g by rw [hgen]; trivial))
    rw [← hn]
    have hnlt : n < 5 := by simpa [hord] using hnlt
    interval_cases n
    · simpa [v] using hvmem 0
    · simpa [v] using hvmem 1
    · simpa [v] using hvmem 2
    · simpa [v] using hvmem 3
    · rw [hrel]
      exact S.mul_mem (S.mul_mem (S.mul_mem (by simpa [v] using hvmem 0)
        (by simpa [v] using hvmem 1)) (hvmem 2)) (hvmem 3)
  have hclosure : closure (Set.range (fun a : A => a • b)) = ⊤ := by
    let T := closure (Set.range (fun a : A => a • b))
    have hf (a : A) (x : V) (hx : x ∈ T) : a • x ∈ T := by
      refine closure_induction (p := fun x _ => a • x ∈ T) ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨c, rfl⟩
        exact subset_closure ⟨a * c, mul_smul a c b⟩
      · simp
      · intro x y _ _ hx hy
        simpa only [smul_mul'] using T.mul_mem hx hy
      · intro x _ hx
        simpa only [smul_inv'] using T.inv_mem hx
    let _ : IsInvariant A V T := ⟨fun a x => ⟨hf a x, fun hx => by
      simpa using hf a⁻¹ (a • x) hx⟩⟩
    rcases invariant_eq_bot_or_top_of_five_actor hA hV hfixed T with hbot | htop
    · exact (hb (hbot.le (show b ∈ T from subset_closure ⟨1, one_smul A b⟩))).elim
    · exact htop
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hclosure]
    exact (closure_le _).mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)
  apply (Nat.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro x
    change x ∈ S
    rw [hS]
    trivial
  · rw [hV, Nat.card_eq_fintype_card]
    decide

end Theory.GroupAction
