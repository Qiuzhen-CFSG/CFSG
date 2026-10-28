module

public import Theory.SpecificGroups.SU3.ExtensionBorel.Actors
public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.Descent.ScalarKernel

/-!
# Two-power root–diagonal–graph actors

A diagonal twist of entrywise Hermitian conjugation has diagonal square.
The diagonal matrix group has odd exponent, so a two-power such actor has
square one. Scalar-centralizer rigidity then gives its root action as
`(a,b) ↦ (c * conj a, conj b)` with `c * conj c = 1`.

For a root twist, a square with zero first coordinate is the identity.
Consequently these twists have no elements of order four, while order eight
is retained. The result applies after removing a root inner actor inside the
original two-group; it requires no conjugator outside the given overgroup.

Source: Huppert II.10.12; GLS3, Theorem 2.5.12 and §2.7; the unitary model
calculation for Aschbacher (1975), Lemma 3.4, pp.94–96.
-/

open Matrix Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
open ExtensionBorel BorelTorus.SemilinearActors EvenInner
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [Finite E] [CharP E 2] in
private theorem diagonal_pow (D : GL (Fin 3) E)
    (hD : ∀ i j, i ≠ j → D.val i j = 0) : D ^ (Nat.card E - 1) = 1 := by
  have he : D.val = Matrix.diagonal (fun i => D.val i i) := by
    ext i j
    by_cases h : i = j
    · subst j; simp
    · simp [h, hD i j h]
  have hn (i : Fin 3) : D.val i i ≠ 0 := by
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) E => A i i) D.val_inv
    rw [he, Matrix.diagonal_mul] at hh
    exact left_ne_zero_of_mul_eq_one (by simpa using hh)
  apply Units.ext
  change D.val ^ (Nat.card E - 1) = 1
  rw [he, Matrix.diagonal_pow]
  have hp (i : Fin 3) : D.val i i ^ (Nat.card E - 1) = 1 := by
    have hh := congrArg Units.val (pow_card_eq_one' (x := Units.mk0 (D.val i i) (hn i)))
    simpa only [Nat.card_units, Units.val_pow_eq_pow_val, Units.val_one, Units.val_mk0] using hh
  change Matrix.diagonal (fun i : Fin 3 => (D.val i i) ^ (Nat.card E - 1)) = 1
  convert Matrix.diagonal_one (n := Fin 3) (α := E) using 1
  congr 1
  funext i
  exact hp i

private theorem actor_pow {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (a : MulAut G) (d : H)
    (ha : ∀ x, f (a x) = d * f x * d⁻¹)
    {m : ℕ} (hd : d ^ m = 1) : a ^ m = 1 := by
  have hp (k : ℕ) (x : G) : f ((a ^ k) x) = d ^ k * f x * (d ^ k)⁻¹ := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, MulAut.mul_apply, ih, ha, pow_succ]
      group
  apply MulEquiv.ext
  intro x
  apply hf
  simpa only [MulAut.one_apply, hd, one_mul, inv_one, mul_one] using hp m x

omit [CharP E 2] in
/-- A diagonal twist of Hermitian conjugation of two-power order has square one. -/
public theorem diagonal_graph_square_one {n : ℕ} (hn : 0 < n)
    (hcard : Nat.card E = (2^n)^2)
    (d : J.unitarySubgroup) (hd : ∀ i j, i ≠ j → d.val.val i j = 0)
    {r : ℕ} (hr : (J.unitaryConj d * fieldActor J hJ J.conj) ^ (2^r) = 1) :
    (J.unitaryConj d * fieldActor J hJ J.conj)^2 = 1 := by
  let a := J.unitaryConj d * fieldActor J hJ J.conj
  let D := d.val * GeneralLinearGroup.map J.conj.toRingHom d.val
  have hD : ∀ i j, i ≠ j → D.val i j = 0 := by
    intro i j hij
    change (d.val.val * d.val.val.map J.conj) i j = 0
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst k
      simp [hd i j hij]
    · simp [hd i k hik]
  have hformula (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      ((a ^ 2) x).val = ProjGenLinGroup.mk D * x.val * (ProjGenLinGroup.mk D)⁻¹ := by
    have hh : ProjGenLinGroup.map J.conj.toRingHom
        (ProjGenLinGroup.map J.conj.toRingHom x.val) = x.val := by
      obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
      rw [← hg]
      rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.map_mk]
      congr 1
      apply Units.ext
      ext i j
      exact J.conj_involutive _
    simp only [a, pow_two, MulAut.mul_apply, J.unitaryConj_apply_val,
      fieldActor_apply_val, map_mul, map_inv, hh, D, ProjGenLinGroup.map_mk]
    group
  have ho : (a^2) ^ (Nat.card E - 1) = 1 :=
    actor_pow (ProjectiveSpecialUnitaryMatrixGroup J).subtype Subtype.val_injective
      (a^2) (ProjGenLinGroup.mk D) hformula
      (by rw [← map_pow, diagonal_pow D hD, map_one])
  have ht : (a^2) ^ (2^r) = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hr, one_pow]
  have hc : Nat.Coprime 2 (Nat.card E - 1) := by
    apply Nat.coprime_two_left.mpr
    rw [hcard]
    have he : Even ((2^n)^2) := (even_two.pow_of_ne_zero (by omega)).pow_of_ne_zero (by decide)
    exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) he odd_one
  exact (pow_eq_one_iff_of_coprime (hc.pow_left r)).mp ⟨ht, ho⟩

private theorem diagonal_graph_norms
    (hconj : ∃ t : E, J.conj t ≠ t)
    (d : J.unitarySubgroup) (hd : ∀ i j, i ≠ j → d.val.val i j = 0)
    (hsq : (J.unitaryConj d * fieldActor J hJ J.conj)^2 = 1) :
    (∀ i, d.val.val i i * J.conj (d.val.val i i) = 1) ∧
      d.val.val 0 0 = d.val.val 2 2 := by
  let a := J.unitaryConj d * fieldActor J hJ J.conj
  let D := d.val * GeneralLinearGroup.map J.conj.toRingHom d.val
  have hformula (x : ProjectiveSpecialUnitaryMatrixGroup J) :
      ((a ^ 2) x).val = ProjGenLinGroup.mk D * x.val * (ProjGenLinGroup.mk D)⁻¹ := by
    have hh : ProjGenLinGroup.map J.conj.toRingHom
        (ProjGenLinGroup.map J.conj.toRingHom x.val) = x.val := by
      obtain ⟨g, hg⟩ := ProjGenLinGroup.mk_surjective x.val
      rw [← hg, ProjGenLinGroup.map_mk, ProjGenLinGroup.map_mk]
      congr 1
      apply Units.ext
      ext i j
      exact J.conj_involutive _
    simp only [a, pow_two, MulAut.mul_apply, J.unitaryConj_apply_val,
      fieldActor_apply_val, map_mul, map_inv, hh, D, ProjGenLinGroup.map_mk]
    group
  have hc : D ∈ center (GL (Fin 3) E) := J.projective_centralizer_scalar hJ hconj D (by
    intro x
    have hh := hformula x
    rw [show a^2 = 1 from hsq, MulAut.one_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm)
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
  have hdiag (i : Fin 3) : d.val.val i i * J.conj (d.val.val i i) = (c : E) := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i i) hc
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hh
    change (c : E) = (d.val.val * d.val.val.map J.conj) i i at hh
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at hh
    · exact hh.symm
    · intro j _ hji
      simp [hd i j (Ne.symm hji)]
    · simp
  have hu := (J.mem_unitarySubgroup_iff _).mp d.property
  rw [hJ] at hu
  have hu11 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hu
  have hu02 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 2) hu
  simp [HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hd] at hu11 hu02
  have hc1 : (c : E) = 1 := (hdiag 1).symm.trans (by simpa only [mul_comm] using hu11)
  have hn (i : Fin 3) : d.val.val i i * J.conj (d.val.val i i) = 1 := by rw [hdiag, hc1]
  refine ⟨hn, ?_⟩
  apply mul_left_cancel₀ (right_ne_zero_of_mul_eq_one (hn 0))
  calc
    J.conj (d.val.val 0 0) * d.val.val 0 0 = 1 := by simpa only [mul_comm] using hn 0
    _ = J.conj (d.val.val 0 0) * d.val.val 2 2 := hu02.symm

private def twistedConj (c : E) (hc : c * J.conj c = 1)
    (z : hermitianUnipotentCoord J) : hermitianUnipotentCoord J :=
  ⟨(c * J.conj z.val.1, J.conj z.val.2), by
    have hh := congrArg J.conj z.property
    simp only [map_add, map_mul, map_zero] at hh
    rw [J.conj_involutive, J.conj_involutive] at hh
    change J.conj z.val.2 + J.conj (J.conj z.val.2) +
      c * J.conj z.val.1 * J.conj (c * J.conj z.val.1) = 0
    rw [map_mul, J.conj_involutive, J.conj_involutive]
    calc
      _ = J.conj z.val.2 + z.val.2 + (c * J.conj c) * (J.conj z.val.1 * z.val.1) := by ring
      _ = 0 := by rw [hc, one_mul]; exact hh⟩

/-- An involutory diagonal graph actor acts by `(c * conj a, conj b)`,
where `c` has norm one. -/
theorem diagonal_graph_root_coordinates
    (hconj : ∃ t : E, J.conj t ≠ t)
    (d : J.unitarySubgroup) (hd : ∀ i j, i ≠ j → d.val.val i j = 0)
    (hsq : (J.unitaryConj d * fieldActor J hJ J.conj)^2 = 1) :
    ∃ c : E, ∃ hc : c * J.conj c = 1,
      ∀ z : hermitianUnipotentCoord J,
        (J.unitaryConj d * fieldActor J hJ J.conj) (hermitianUnipotentPSU J hJ z) =
          hermitianUnipotentPSU J hJ (twistedConj J c hc z) := by
  obtain ⟨hn, he⟩ := diagonal_graph_norms J hJ hconj d hd hsq
  let c := d.val.val 0 0 / d.val.val 1 1
  have hc : c * J.conj c = 1 := by
    dsimp [c]
    rw [map_div₀, div_mul_div_comm, hn 0, hn 1, div_self one_ne_zero]
  refine ⟨c, hc, fun z => ?_⟩
  have h01 : c * d.val.val 1 1 = d.val.val 0 0 := div_mul_cancel₀ _
    (left_ne_zero_of_mul_eq_one (hn 1))
  have h12 : J.conj c * d.val.val 2 2 = d.val.val 1 1 := by
    have h0 := hn 0
    have h1 := hn 1
    dsimp [c]
    rw [map_div₀, ← he]
    apply (div_mul_eq_mul_div _ _ _).trans
    rw [mul_comm (J.conj (d.val.val 0 0)), h0]
    exact (eq_div_iff (right_ne_zero_of_mul_eq_one h1)).mpr h1 |>.symm
  have hm : d.val * GeneralLinearGroup.map J.conj.toRingHom (hermitianUnipotentGL J z) =
      hermitianUnipotentGL J (twistedConj J c hc z) * d.val := by
    apply Units.ext
    ext i j
    have h12' : J.conj c * d.val.val 0 0 = d.val.val 1 1 := he.symm ▸ h12
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hermitianUnipotentMatrix,
        twistedConj, hd, map_mul, CharTwo.neg_eq, ← he]
    · linear_combination -(J.conj z.val.1) * h01
    · exact mul_comm _ _
    · linear_combination -(J.conj (J.conj z.val.1)) * h12'
  apply Subtype.ext
  change _ = ProjGenLinGroup.mk (hermitianUnipotentGL J (twistedConj J c hc z))
  rw [MulAut.mul_apply, J.unitaryConj_apply_val, fieldActor_apply_val]
  change ProjGenLinGroup.mk d.val *
      ProjGenLinGroup.map J.conj.toRingHom (ProjGenLinGroup.mk (hermitianUnipotentGL J z)) * _ = _
  rw [ProjGenLinGroup.map_mk, ← map_mul, hm, map_mul]
  simp

omit [Finite E] in
private theorem twisted_product_square_one (c : E) (hc : c * J.conj c = 1)
    (z : hermitianUnipotentCoord J)
    (hsq : (z * twistedConj J c hc z)^2 = 1) : z * twistedConj J c hc z = 1 := by
  have ht : z.val.1 + c * J.conj z.val.1 = 0 :=
    (BinaryRootFrattini.square_one_iff J _).mp hsq
  have hb := z.property
  apply Subtype.ext
  apply Prod.ext ht
  change z.val.2 + J.conj z.val.2 - z.val.1 * J.conj (c * J.conj z.val.1) = 0
  rw [map_mul, J.conj_involutive, CharTwo.sub_eq_add]
  have he : z.val.1 = c * J.conj z.val.1 := (eq_neg_of_add_eq_zero_left ht).trans (CharTwo.neg_eq _)
  have ha : J.conj c * z.val.1 = J.conj z.val.1 := by
    calc
      J.conj c * z.val.1 = J.conj c * (c * J.conj z.val.1) := congrArg _ he
      _ = (c * J.conj c) * J.conj z.val.1 := by ring
      _ = J.conj z.val.1 := by rw [hc, one_mul]
  rw [ha]
  exact hb

private theorem inner_twist_square {G : Type*} [Group G] (x : G) (a : MulAut G) :
    (MulAut.conj x * a)^2 = MulAut.conj (x * a x) * a^2 := by
  ext y
  simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

/-- A root twist of an involutory diagonal graph actor cannot have order four.
It can have order eight, whose square is a noncentral root element. -/
public theorem root_diagonal_graph_fourth
    (hconj : ∃ t : E, J.conj t ≠ t)
    (hi : Function.Injective (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _))
    (d : J.unitarySubgroup) (hd : ∀ i j, i ≠ j → d.val.val i j = 0)
    (hsq : (J.unitaryConj d * fieldActor J hJ J.conj)^2 = 1)
    (z : hermitianUnipotentCoord J)
    (hfour : (MulAut.conj (hermitianUnipotentPSU J hJ z) *
      (J.unitaryConj d * fieldActor J hJ J.conj))^4 = 1) :
    (MulAut.conj (hermitianUnipotentPSU J hJ z) *
      (J.unitaryConj d * fieldActor J hJ J.conj))^2 = 1 := by
  obtain ⟨c, hc, hact⟩ := diagonal_graph_root_coordinates J hJ hconj d hd hsq
  let a := MulAut.conj (hermitianUnipotentPSU J hJ z) *
    (J.unitaryConj d * fieldActor J hJ J.conj)
  let w := z * twistedConj J c hc z
  have he : a^2 = MulAut.conj (hermitianUnipotentPSU J hJ w) := by
    rw [inner_twist_square, hsq, mul_one, hact, ← map_mul]
  have hw : w^2 = 1 := by
    apply OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ
    apply hi
    rw [map_pow, map_pow, map_one, map_one, ← he, ← pow_mul]
    exact hfour
  have hw1 := twisted_product_square_one J c hc z hw
  rw [he, show w = 1 from hw1, map_one, map_one]

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
