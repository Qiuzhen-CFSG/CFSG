module

public import Theory.SpecificGroups.PSL4Three.LocalThree.Model
public import Theory.FieldTheory.Nine
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-!
# Ordinary centralizers of commuting SL₄(3) lifts

Extend scalars faithfully from F₃ to F₉ and rescale the two lifts to
involutions. The three trace identities make the four joint projectors
nonzero. Their images contain four independent vectors, hence are lines.
A commuting element of order three fixes each line pointwise and is the
identity. Cauchy's theorem excludes three from the common centralizer.

The projector argument is adapted from the corresponding existing
`ClassicalUnitary/UnitaryFourThree/ElementaryLocal/FourCentralizer/Commuting`
module; no unitary-group premise or model comparison is used.
Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4), printed p.482 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Matrix Module
namespace Matrix.PSL4Three.LocalThree.FourCentralizer

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

private abbrev extend : Mat →+* M := (algebraMap (ZMod 3) K).mapMatrix

private lemma extend_injective : Function.Injective extend := by
  intro A B h
  apply Matrix.ext
  intro i j
  exact (algebraMap (ZMod 3) K).injective (congrArg (fun T : M => T i j) h)

private lemma extend_trace (A : Mat) : trace (extend A) = algebraMap (ZMod 3) K (trace A) :=
  (AddMonoidHom.map_trace (algebraMap (ZMod 3) K) A).symm

/-- Each possible scalar square has a square root after the faithful extension to F₉. -/
private lemma rescale (a : SL) (ha : (project a) ^ 2 = 1) :
    ∃ c : K, (c • extend (a : Mat)) * (c • extend (a : Mat)) = 1 := by
  obtain ⟨u, hu, hua⟩ := square_scalar a ha
  obtain ⟨c, hc⟩ := (show ∀ u : ZMod 3, u ^ 2 = 1 →
    ∃ c : K, c * c * algebraMap (ZMod 3) K u = 1 from by decide) u hu
  have he : extend (a : Mat) * extend (a : Mat) =
      algebraMap (ZMod 3) K u • (1 : M) := by
    rw [← map_mul, ← pow_two, hua]
    apply Matrix.ext
    intro i j
    simp only [extend, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨c, ?_⟩
  rw [smul_mul_smul_comm, he, smul_smul, hc, one_smul]

/-- The common centralizer of commuting lifts has no factor of nine.
The trace assumptions concern both lifts and their product. -/
theorem commuting_lift_centralizer_not_nine_dvd (a b : SL)
    (ha : (project a) ^ 2 = 1) (hb : (project b) ^ 2 = 1)
    (hab : Commute a b) (htra : trace (a : Mat) = 0)
    (htrb : trace (b : Mat) = 0) (htrab : trace ((a * b : SL) : Mat) = 0) :
    ¬ 3 ^ 2 ∣ Nat.card (Subgroup.centralizer ({a, b} : Set SL)) := by
  obtain ⟨c, hc⟩ := rescale a ha
  obtain ⟨d, hd⟩ := rescale b hb
  intro hdiv
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({a, b} : Set SL))
    3 ((show 3 ∣ 3 ^ 2 by decide).trans hdiv)
  have hx3 : x ^ 3 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
  have hxm : ((x : SL) : Mat) ^ 3 = 1 := congrArg (fun y : Subgroup.centralizer ({a, b} : Set SL) => ((y : SL) : Mat)) hx3
  have hxa : Commute ((x : SL) : Mat) (a : Mat) :=
    congrArg (fun y : SL => (y : Mat))
      ((Subgroup.mem_centralizer_iff.mp x.property) a (by simp)).symm
  have hxb : Commute ((x : SL) : Mat) (b : Mat) :=
    congrArg (fun y : SL => (y : Mat))
      ((Subgroup.mem_centralizer_iff.mp x.property) b (by simp)).symm
  have habm : Commute (a : Mat) (b : Mat) := congrArg (fun y : SL => (y : Mat)) hab.eq
  have hx1 : extend ((x : SL) : Mat) = 1 := by
    apply commuting_matrix_cube (c • extend (a : Mat)) (d • extend (b : Mat)) _ hc hd
      (((habm.map extend).smul_left c).smul_right d)
    · rw [trace_smul, extend_trace, htra, map_zero, smul_zero]
    · rw [trace_smul, extend_trace, htrb, map_zero, smul_zero]
    · rw [smul_mul_smul_comm, trace_smul, ← map_mul, extend_trace]
      change (c * d) • algebraMap (ZMod 3) K (trace ((a * b : SL) : Mat)) = 0
      rw [htrab, map_zero, smul_zero]
    · exact (hxa.map extend).smul_right c
    · exact (hxb.map extend).smul_right d
    · rw [← map_pow, hxm, map_one]
  have hxone : x = 1 := Subtype.ext (Subtype.ext
    (extend_injective (hx1.trans (map_one extend).symm)))
  rw [hxone, orderOf_one] at hx
  norm_num at hx

end Matrix.PSL4Three.LocalThree.FourCentralizer
