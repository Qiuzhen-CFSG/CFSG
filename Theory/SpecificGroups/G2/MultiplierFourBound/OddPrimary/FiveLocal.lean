module

public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks
public import Mathlib.Tactic.IntervalCases

/-!
# An order-25 Sylow subgroup with partial inversion in G₂(4)

Choose a nonidentity unit a of GF(4), so a² = a+1. The orthogonal long-
and short-root elements E(a)r and C(a)(rs)³r have order five and commute.
Two octonion coordinates distinguish their 25 products. The root involution
E(a) inverts the long element and commutes with the short element. The
checked group order makes their subgroup Sylow.

The coordinate construction extends the cubic construction in
`Theory.AtlasPort.LinearGroups.G2.EvenThreeRank`. The underlying root and
Weyl formulas are the licensed work of Gerald Höhn and the ATLAS contributors;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No finite-field carrier
is replaced: the final witness lives in Model (GaloisField 2 2).
Source application: Aschbacher–Smith I.1.3(1), GLS III §6.1.
-/

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion Subgroup
open scoped CharTwo
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary.FiveLocal
variable {K : Type*} [Field K] [CharP K 2]

def long (a : K) : Model K := rootE a * weylR
def short (a : K) : Model K := rootC a * ((weylR * weylS)^3 * weylR)

theorem long_apply (a : K) (v : Carrier K) :
    (long a).val v = ![v 0, a * v 1 + v 2, v 1, v 3, v 4,
      a * v 5 + v 6, v 5, v 7] := by
  funext i
  fin_cases i <;> simp [long, rootE, rootEEquiv, rootELinear, rootEApply,
    weylR, weylREquiv, weylRLinear, weylRApply, CharTwo.neg_eq, CharTwo.sub_eq_add, add_comm]

theorem short_apply (a : K) (v : Carrier K) :
    (short a).val v =
      ![a^2 * v 0 + a * v 3 + a * v 4 + v 7,
        a * v 1 + v 5, a * v 2 + v 6, a * v 0 + v 4,
        a * v 0 + v 3, v 1, v 2, v 0] := by
  funext i
  fin_cases i <;> simp [short, rootC, rootCEquiv, rootCLinear, rootCApply,
    weylR, weylREquiv, weylRLinear, weylRApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, pow_succ, CharTwo.neg_eq,
    CharTwo.sub_eq_add, add_comm, add_left_comm, add_assoc]

theorem long_short (a b : K) : Commute (long a) (short b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (long a).val ((short b).val v) = (short b).val ((long a).val v)
  rw [long_apply, short_apply, long_apply, short_apply]
  funext i
  fin_cases i <;> simp <;> ring

theorem rootE_short (a b : K) : Commute (rootE a) (short b) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (rootE a).val ((short b).val v) = (short b).val ((rootE a).val v)
  simp only [short_apply]
  funext i
  fin_cases i <;> simp [rootE, rootEEquiv, rootELinear, rootEApply,
    CharTwo.neg_eq, CharTwo.sub_eq_add] <;> ring

theorem rootE_inverts_long (a : K) :
    rootE a * long a * (rootE a)⁻¹ = (long a)⁻¹ := by
  have he : rootE a * rootE a = (1 : Model K) := by
    rw [rootE_add, CharTwo.add_self_eq_zero]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    funext i
    fin_cases i <;> simp [rootE, rootEEquiv, rootELinear, rootEApply]
  have hw : (weylR : Model K)⁻¹ = weylR := inv_eq_of_mul_eq_one_right (by
    simpa only [pow_two] using (weylR_sq (K := K)))
  simp only [long, ← mul_assoc, he, one_mul, mul_inv_rev, hw]

theorem parameter_cube (a : K) (ha : a^2 = a+1) : a^3 = 1 := by
  rw [pow_succ, ha]
  ring_nf
  simp [ha]

theorem long_fifth (a : K) (ha : a^2 = a+1) : (long a)^5 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (long a).val ((long a).val ((long a).val ((long a).val ((long a).val v)))) = v
  simp only [long_apply]
  funext i
  fin_cases i <;> simp <;> ring_nf <;>
    simp [pow_eq_pow_mod 3 (parameter_cube a ha), pow_eq_pow_mod 4 (parameter_cube a ha),
      pow_eq_pow_mod 5 (parameter_cube a ha), pow_eq_pow_mod 6 (parameter_cube a ha),
      pow_eq_pow_mod 7 (parameter_cube a ha), pow_eq_pow_mod 8 (parameter_cube a ha),
      pow_eq_pow_mod 9 (parameter_cube a ha), pow_eq_pow_mod 10 (parameter_cube a ha), ha] <;>
    ring_nf <;> simp

theorem short_fifth (a : K) (ha : a^2 = a+1) : (short a)^5 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (short a).val ((short a).val ((short a).val ((short a).val ((short a).val v)))) = v
  simp only [short_apply]
  funext i
  fin_cases i <;> simp <;> ring_nf <;>
    simp [pow_eq_pow_mod 3 (parameter_cube a ha), pow_eq_pow_mod 4 (parameter_cube a ha),
      pow_eq_pow_mod 5 (parameter_cube a ha), pow_eq_pow_mod 6 (parameter_cube a ha),
      pow_eq_pow_mod 7 (parameter_cube a ha), pow_eq_pow_mod 8 (parameter_cube a ha),
      pow_eq_pow_mod 9 (parameter_cube a ha), pow_eq_pow_mod 10 (parameter_cube a ha), ha] <;>
    ring_nf <;> simp

private def fifthHom (g : Model K) (hg : g^5=1) : Multiplicative (ZMod 5) →* Model K where
  toFun a := g ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    change g ^ (a.toAdd + b.toAdd).val = g ^ a.toAdd.val * g ^ b.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ hg).symm

private abbrev Pair := Multiplicative (ZMod 5) × Multiplicative (ZMod 5)
def embedding (a : K) (ha : a^2 = a+1) : Pair →* Model K :=
  (fifthHom (long a) (long_fifth a ha)).noncommCoprod
    (fifthHom (short a) (short_fifth a ha))
    (fun i j => (long_short a a).pow_pow i.toAdd.val j.toAdd.val)

theorem long_pow_last (a : K) (n : ℕ) (v : Carrier K) :
    ((long a)^n).val v 7 = v 7 := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    change ((long a)^n).val ((long a).val v) 7 = v 7
    rw [ih, long_apply]
    rfl

theorem embedding_injective (a : K) (ha : a^2 = a+1) (ha0 : a ≠ 0) :
    Function.Injective (embedding a ha) := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨i,j⟩ hij
  have h0 := congrArg (fun g : Model K => g.val (basisVector 0) 7) hij
  change ((long a)^i.toAdd.val).val (((short a)^j.toAdd.val).val (basisVector 0)) 7 = 0 at h0
  rw [long_pow_last] at h0
  have hj : j.toAdd.val = 0 := by
    have hjlt := ZMod.val_lt j.toAdd
    interval_cases hjn : j.toAdd.val
    · rfl
    all_goals simp [pow_succ, short_apply, basisVector] at h0
    all_goals try ring_nf at h0
    all_goals try simp [pow_eq_pow_mod 3 (parameter_cube a ha),
      pow_eq_pow_mod 4 (parameter_cube a ha), pow_eq_pow_mod 5 (parameter_cube a ha),
      pow_eq_pow_mod 6 (parameter_cube a ha), ha] at h0
    all_goals first
    | exact False.elim (ha0 h0)
    | exact False.elim ((pow_ne_zero 2 ha0) (ha.trans (by simpa [add_comm] using h0)))
  have h1 := congrArg (fun g : Model K => g.val (basisVector 1) 2) hij
  change (((long a)^i.toAdd.val * (short a)^j.toAdd.val).val (basisVector 1)) 2 = 0 at h1
  simp only [hj, pow_zero, mul_one] at h1
  have hi : i.toAdd.val = 0 := by
    have hilt := ZMod.val_lt i.toAdd
    interval_cases hin : i.toAdd.val
    · rfl
    all_goals simp [pow_succ, long_apply, basisVector] at h1
    all_goals ring_nf at h1
    all_goals try simp [pow_eq_pow_mod 3 (parameter_cube a ha), ha] at h1
    all_goals apply False.elim; apply ha0; simpa [add_assoc, add_left_comm] using h1
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    exact hi
  · apply Multiplicative.toAdd.injective
    apply ZMod.val_injective
    exact hj

theorem pair_generates (a : K) (ha : a^2 = a+1) :
    Subgroup.closure ({long a, short a} : Set (Model K)) = (embedding a ha).range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | hg
    · exact ⟨(Multiplicative.ofAdd 1, 1), by
        change (long a)^1 * (short a)^0 = long a
        simp⟩
    · obtain rfl := hg
      exact ⟨(1, Multiplicative.ofAdd 1), by
        change (long a)^0 * (short a)^1 = short a
        simp⟩
  · have hx : long a ∈ Subgroup.closure ({long a, short a} : Set (Model K)) :=
      Subgroup.subset_closure (by simp)
    have hy : short a ∈ Subgroup.closure ({long a, short a} : Set (Model K)) :=
      Subgroup.subset_closure (by simp)
    rintro g ⟨⟨i,j⟩,rfl⟩
    exact mul_mem (pow_mem hx _) (pow_mem hy _)

end Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary.FiveLocal

namespace Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary
open FiveLocal Subgroup

private theorem exists_parameter : ∃ a : FourField, a ≠ 0 ∧ a^2 = a+1 := by
  have hu : Nat.card FourFieldˣ = 3 := by
    rw [Nat.card_units, GaloisField.card 2 2 (by decide)]
    norm_num
  let : Nontrivial FourFieldˣ := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  obtain ⟨u, hune⟩ := exists_ne (1 : FourFieldˣ)
  have hcube : (u : FourField)^3 = 1 := by
    have h := pow_card_eq_one' (x := u)
    rw [hu] at h
    exact congrArg Units.val h
  have hu1 : (u : FourField) ≠ 1 := fun h => hune (Units.ext h)
  have hprod : ((u : FourField)-1) * ((u : FourField)^2 + u + 1) = 0 := by
    calc
      _ = (u : FourField)^3 - 1 := by ring
      _ = 0 := by rw [hcube, sub_self]
  have hp : (u : FourField)^2 + ((u : FourField)+1) = 0 := by
    rw [← add_assoc]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hu1)
  exact ⟨u, Units.ne_zero u, by simpa using (eq_neg_of_add_eq_zero_left hp)⟩

public theorem exists_five_configuration :
    ∃ (Q : Sylow 5 FourBase) (x y r : FourBase),
      closure ({x, y} : Set FourBase) = (Q : Subgroup FourBase) ∧
      x^5 = 1 ∧ Commute x y ∧ r*x*r⁻¹ = x⁻¹ ∧ Commute r y := by
  obtain ⟨a, ha0, ha⟩ := exists_parameter
  let S : Subgroup FourBase := (embedding a ha).range
  have hS : Nat.card S = 25 := by
    change Nat.card (embedding a ha).range = 25
    rw [← Nat.card_congr (MonoidHom.ofInjective (embedding_injective a ha ha0)).toEquiv]
    simp [Pair, Nat.card_eq_fintype_card]
  have hindex : S.index = 10063872 := by
    have h := S.card_mul_index
    rw [hS, OrderChecks.four_order] at h
    omega
  let Q : Sylow 5 FourBase := (IsPGroup.of_card (show Nat.card S = 5^2 from hS)).toSylow
    (by rw [hindex]; decide)
  exact ⟨Q, long a, short a, rootE a, pair_generates a ha,
    long_fifth a ha, long_short a a, rootE_inverts_long a, rootE_short a a⟩

end Atlas.G2.FiniteCover.MultiplierFourBound.OddPrimary
