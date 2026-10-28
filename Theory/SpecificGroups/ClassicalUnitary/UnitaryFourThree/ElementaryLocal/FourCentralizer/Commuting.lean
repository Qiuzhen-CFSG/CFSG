module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer.Lifts
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Ordinary centralizers of commuting SU₄(3) lifts

Projective involution lifts square to fourth-root scalar matrices. Every such
scalar in Nine has a square root, so rescaling gives commuting involutions A, B.
The three trace equations make all four joint spectral projectors have trace one.
Their nonzero images contain four independent vectors, which form a basis in
ambient dimension four. Thus each joint space is a line, with its dimension
established over the integers rather than inferred from characteristic-three traces.

A commuting element of order three acts by scalars on these lines. Nine has no
nonidentity cube root of one, so that element is the identity. Cauchy's theorem
excludes three, and hence nine, from the order of the ordinary centralizer.

This proves the commuting input of `four_centralizer_not_nine_dvd_of_lift_bounds`.
The projective assembly and the source of the trace equations remain separate.
Source: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4, repeated as Theorem
0.1.1(4), printed p.482 of `refs/quasithin.pdf`; SU/PSU conventions in GLS3,
chapter 2 (`refs/KGroup/GLS3/chapter2.tex`).
-/

public noncomputable section

open Matrix Module BenderSuzuki.MatrixGroups

namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer

private abbrev K := FiniteField.Nine
private abbrev V := Fin 4 → K
private abbrev I := Bool × Bool

/-- Four nonzero orthogonal projectors give four independent vectors and hence a basis.
Their images are therefore lines; no characteristic-three trace is read as an integer rank. -/
private lemma projector_basis (P : I → Module.End K V)
    (hP : ∀ i j, P i * P j = if i = j then P i else 0)
    (hne : ∀ i, P i ≠ 0) :
    ∃ b : Basis I K V, ∀ i v, P i v = b.repr v i • b i := by
  classical
  have hex (i : I) : ∃ w, P i w ≠ 0 := by
    by_contra! h
    exact hne i (LinearMap.ext h)
  choose w hw using hex
  let v : I → V := fun i => P i (w i)
  have hv (i : I) : v i ≠ 0 := hw i
  have hact (i j : I) : P i (v j) = if i = j then v i else 0 := by
    change (P i * P j) (w j) = _
    rw [hP]
    split_ifs with h
    · subst j; rfl
    · rfl
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have he := congrArg (P i) hc
    simp only [map_sum, map_smul, map_zero, hact] at he
    simp only [smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at he
    exact (smul_eq_zero.mp he).resolve_right (hv i)
  let b : Basis I K V := basisOfLinearIndependentOfCardEqFinrank hli (by simp [I, V])
  have hb : ∀ i, b i = v i := fun _ => congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli _) _
  refine ⟨b, ?_⟩
  intro i z
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, map_smul, hb, hact, smul_ite, smul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

private lemma centralizing_cube (P : I → Module.End K V)
    (hP : ∀ i j, P i * P j = if i = j then P i else 0)
    (hne : ∀ i, P i ≠ 0)
    (x : Module.End K V) (hx : x ^ 3 = 1)
    (hc : ∀ i, Commute x (P i)) : x = 1 := by
  obtain ⟨b, hb⟩ := projector_basis P hP hne
  have hv (i : I) : P i (b i) = b i := by simp [hb]
  have hs (i : I) : x (b i) = b.repr (x (b i)) i • b i := by
    rw [← hb, ← Module.End.mul_apply, ← (hc i).eq, Module.End.mul_apply, hv]
  apply b.ext
  intro i
  let c := b.repr (x (b i)) i
  have hsi : x (b i) = c • b i := hs i
  have he : c ^ 3 • b i = b i := by
    calc
      c ^ 3 • b i = (x ^ 3) (b i) := by
        simp only [pow_succ, pow_zero, Module.End.mul_apply,
          hsi, map_smul, smul_smul, one_mul, mul_assoc]
      _ = b i := by rw [hx]; rfl
  have hc3 : c ^ 3 = 1 := (smul_left_injective K (b.ne_zero i)) (by simpa using he)
  have c1 : c = 1 := (show ∀ t : K, t ^ 3 = 1 → t = 1 from by decide) c hc3
  change x (b i) = b i
  rw [hs i]
  change c • b i = b i
  rw [c1, one_smul]

private abbrev M := Matrix (Fin 4) (Fin 4) K

/-- The two spectral projectors of an involution: in characteristic three,
`(1 ± A) / 2` is `-1 ∓ A`. -/
private def half (A : M) (s : Bool) : M := (if s then A else -A) - 1

private lemma add_self_matrix (A : M) : A + A = -A := by
  apply Matrix.ext
  intro i j
  exact (show ∀ x : K, x + x = -x from by decide) (A i j)

private lemma half_mul (A : M) (hA : A * A = 1) (s t : Bool) :
    half A s * half A t = if s = t then half A s else 0 := by
  have hp (X : M) (hX : X * X = 1) : (X - 1) * (X - 1) = X - 1 := by
    calc
      _ = (X * X + 1) - (X + X) := by noncomm_ring
      _ = X - 1 := by rw [hX, add_self_matrix, add_self_matrix]; abel
  have hn : (-A) * (-A) = 1 := by simpa using hA
  cases s <;> cases t <;> simp only [half, Bool.false_eq_true, ↓reduceIte]
  · exact hp (-A) hn
  · noncomm_ring [hA]
  · noncomm_ring [hA]
  · exact hp A hA

private lemma half_commute (A B : M) (hc : Commute A B) (s t : Bool) :
    Commute (half A s) (half B t) := by
  cases s <;> cases t <;> simp only [half, Bool.false_eq_true, ↓reduceIte]
  · exact (hc.neg_left.neg_right.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  · exact (hc.neg_left.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  · exact (hc.neg_right.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  · exact (hc.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)

private def joint (A B : M) (i : I) : M := half A i.1 * half B i.2

private lemma joint_mul (A B : M) (hA : A * A = 1) (hB : B * B = 1)
    (hc : Commute A B) (i j : I) :
    joint A B i * joint A B j = if i = j then joint A B i else 0 := by
  unfold joint
  rw [(half_commute B A hc.symm i.2 j.1).mul_mul_mul_comm,
    half_mul A hA, half_mul B hB]
  by_cases h1 : i.1 = j.1 <;> by_cases h2 : i.2 = j.2 <;>
    simp [h1, h2, Prod.ext_iff]

private lemma joint_trace (A B : M) (hA : trace A = 0) (hB : trace B = 0)
    (hAB : trace (A * B) = 0) (i : I) : trace (joint A B i) = 1 := by
  rcases i with ⟨s, t⟩
  cases s <;> cases t <;>
    simp [joint, half, sub_mul, mul_sub, hA, hB, hAB, trace_one]
  all_goals decide

private lemma commuting_matrix_cube (A B X : M)
    (hA : A * A = 1) (hB : B * B = 1) (hc : Commute A B)
    (htA : trace A = 0) (htB : trace B = 0) (htAB : trace (A * B) = 0)
    (hxA : Commute X A) (hxB : Commute X B) (hx : X ^ 3 = 1) : X = 1 := by
  let P : I → Module.End K V := fun i => Matrix.toLin' (joint A B i)
  have hP (i j : I) : P i * P j = if i = j then P i else 0 := by
    change Matrix.toLin' (joint A B i) * Matrix.toLin' (joint A B j) = _
    change (Matrix.toLin' (joint A B i)).comp (Matrix.toLin' (joint A B j)) = _
    rw [← Matrix.toLin'_mul]
    rw [joint_mul A B hA hB hc]
    split_ifs <;> simp [P]
  have hn (i : I) : P i ≠ 0 := by
    intro he
    have he' : joint A B i = 0 := Matrix.toLin'.injective (by simpa only [map_zero] using he)
    have ht := joint_trace A B htA htB htAB i
    rw [he', trace_zero] at ht
    exact zero_ne_one ht
  have hcX (i : I) : Commute (Matrix.toLin' X) (P i) := by
    have hhalf (Y : M) (hY : Commute X Y) (s : Bool) : Commute X (half Y s) := by
      cases s <;> simp only [half, Bool.false_eq_true, ↓reduceIte]
      · exact hY.neg_right.sub_right (Commute.one_right _)
      · exact hY.sub_right (Commute.one_right _)
    have hh := (hhalf A hxA i.1).mul_right (hhalf B hxB i.2)
    change Matrix.toLin' X * Matrix.toLin' (joint A B i) =
      Matrix.toLin' (joint A B i) * Matrix.toLin' X
    change (Matrix.toLin' X).comp (Matrix.toLin' (joint A B i)) =
      (Matrix.toLin' (joint A B i)).comp (Matrix.toLin' X)
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
    exact congrArg Matrix.toLin' hh.eq
  apply Matrix.toLin'.injective
  simpa only [Matrix.toLin'_one, Module.End.one_eq_id] using centralizing_cube P hP hn (Matrix.toLin' X)
    (by rw [← Matrix.toLin'_pow, hx, Matrix.toLin'_one]; rfl) hcX

/-- A fourth-root scalar in Nine is a square, so each lift can be rescaled
to an involution in the full matrix algebra. -/
private lemma rescale (a : SU) (ha : (project 4 a) ^ 2 = 1) :
    ∃ c : K, (c • a.val.val) * (c • a.val.val) = 1 := by
  have hk : a ^ 2 ∈ (project 4).ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_pow, ha]
  obtain ⟨u, hu, hua⟩ := (IsotropicStabilizers.mem_project_kernel_iff (form 4) _).mp hk
  have hu4 : (u : K) ^ 4 = 1 := congrArg Units.val hu
  obtain ⟨c, hc⟩ := (show ∀ u : K, u ^ 4 = 1 → ∃ c : K, c * c * u = 1 from by decide) u hu4
  refine ⟨c, ?_⟩
  have ha2 : a.val.val * a.val.val = (u : K) • (1 : M) := by
    have he := congrArg Units.val hua
    change (GeneralLinearGroup.scalar (Fin 4) u).val = a.val.val ^ 2 at he
    rw [← pow_two, ← he, GeneralLinearGroup.coe_scalar]
    apply Matrix.ext
    intro i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [smul_mul_smul_comm, ha2, smul_smul, hc, one_smul]

/-- The ordinary centralizer of two commuting lifts has no factor of nine,
using precisely the three trace equations supplied by the projective assembly. -/
theorem commuting_lift_centralizer_not_nine_dvd (a b : SU)
    (ha : (project 4 a) ^ 2 = 1) (hb : (project 4 b) ^ 2 = 1)
    (hab : Commute a b) (htra : Matrix.trace a.val.val = 0)
    (htrb : Matrix.trace b.val.val = 0) (htrab : Matrix.trace (a * b).val.val = 0) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SU)) := by
  obtain ⟨c, hc⟩ := rescale a ha
  obtain ⟨d, hd⟩ := rescale b hb
  intro hdiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({a, b} : Set SU))
    3 ((show 3 ∣ 3 ^ 2 by decide).trans hdiv)
  have hx3 : x ^ 3 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hxm : x.val.val.val ^ 3 = 1 := congrArg (fun y => y.val.val.val) hx3
  have hxa : Commute x.val.val.val a.val.val :=
    congrArg (fun y : SU => y.val.val)
      ((Subgroup.mem_centralizer_iff.mp x.property) a (by simp)).symm
  have hxb : Commute x.val.val.val b.val.val :=
    congrArg (fun y : SU => y.val.val)
      ((Subgroup.mem_centralizer_iff.mp x.property) b (by simp)).symm
  have habm : Commute a.val.val b.val.val := congrArg (fun y : SU => y.val.val) hab.eq
  have hx1 : x.val.val.val = 1 := by
    apply commuting_matrix_cube (c • a.val.val) (d • b.val.val) _ hc hd
      ((habm.smul_left c).smul_right d)
    · rw [Matrix.trace_smul, htra, smul_zero]
    · rw [Matrix.trace_smul, htrb, smul_zero]
    · rw [smul_mul_smul_comm, Matrix.trace_smul]
      change (c * d) • Matrix.trace (a * b).val.val = 0
      rw [htrab, smul_zero]
    · exact hxa.smul_right c
    · exact hxb.smul_right d
    · exact hxm
  have hxone : x = 1 := Subtype.ext (Subtype.ext (Units.ext hx1))
  rw [hxone, orderOf_one] at hx
  norm_num at hx

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ElementaryLocal.FourCentralizer
