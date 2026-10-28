module
public import Theory.GroupAction.FullThreeCommonDisplacement
public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupAction.QuadraticDisplacementInvariantObstruction
public import Theory.GroupAction.SubgroupConjugation

/-!
# Odd centralizers of small quadratic Klein-four actions

Let F and K be odd-order automorphism subgroups of a finite elementary
abelian two-group W. If F acts fully, [F,J]=F for a quadratic subgroup J
of order four, and [W,J] has order at most four, then any K centralizing
both F and J is trivial. No prime-power or solvability assumption on F
is necessary.

The small-displacement centralizer reduction makes a putative nontrivial
K cyclic of order three and fixed-point-free on W. Its invariant nonzero
subgroups of order at most four have order four. Thus all three
nonidentity actors of J have the same displacement [W,J]. The proved
Klein-four factorization writes F as a product of their centralizers;
each centralizer preserves the corresponding displacement. Therefore
[W,J] is F-invariant, and the full-commutator quotient argument forces it
to be all of W. Quadraticity would make J act trivially, a contradiction.

This supplies the initial-center-kernel elimination implicit in
Stellmacher (9.1)(10), Journal of Algebra 190 (1997), p.47. The
Klein-four factorization is the standard Brauer–Wielandt coprime-action
argument, exported by `KleinFourFactorization`. This module has no
Stellmacher campaign dependency.
-/

open scoped IsMulCommutative

public theorem quadratic_four_odd_centralizer_eq_bot
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (F J K : Subgroup (MulAut W))
    (hFodd : Odd (Nat.card F)) (hKodd : Odd (Nat.card K))
    (hfull : commutatorAction F W = ⊤) (hgenerate : ⁅F, J⁆ = F)
    (hJcard : Nat.card J = 4) (hquadratic : commutatorAction₂ J W = ⊥)
    (hsmall : Nat.card (commutatorAction J W) ≤ 4)
    (hKF : ⁅K, F⁆ = ⊥) (hKJ : ⁅K, J⁆ = ⊥) : K = ⊥ := by
  classical
  by_contra hKne
  obtain ⟨hKcard, hDcard, hKfull⟩ :=
    QuadraticFourCentralizer.nontrivial_odd_centralizer_full_three F J K
      hfull hgenerate hsmall hKodd hKne hKF hKJ
  let _ : IsElementaryAbelian 2 J :=
    QuadraticFourCentralizer.elementaryAbelian_of_quadratic J hquadratic
  let _ : Nontrivial J := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, hane⟩ := exists_ne (1 : J)
  obtain ⟨b, hbne, hba⟩ := ENat.exists_ne_ne_of_three_le (α := J)
    (by norm_num [ENat.card_eq_coe_natCard, hJcard]) 1 a
  have square (j : J) : j ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 J) j
  have hab : Commute a b := (IsMulCommutative.is_comm (M := J)).comm a b
  have habne : a * b ≠ 1 := by
    intro heq
    apply hba
    have haInv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using square a)
    exact (eq_inv_of_mul_eq_one_right heq).trans haInv
  let D := commutatorAction J W
  let stabilizer : Subgroup (MulAut W) :=
    { carrier := {actor | ∀ point : W, point ∈ D ↔ actor point ∈ D}
      one_mem' := by simp
      mul_mem' := by
        intro first second hfirst hsecond point
        exact (hsecond point).trans (hfirst (second point))
      inv_mem' := by
        intro actor hactor point
        simpa using (hactor (actor⁻¹ point)).symm }
  have hJF : J ≤ Subgroup.normalizer (F : Set (MulAut W)) :=
    QuadraticFourCentralizer.normalizes_of_commutator_eq F J hgenerate
  let _ : MulDistribMulAction J F := Subgroup.conjMulDistribMulActionOfLeNormalizer J F hJF
  let action : J →* MulAut F := MulDistribMulAction.toMulAut J F
  have hfixed (j : J) (hjne : j ≠ 1) (x : F) (hx : action j x = x) :
      (x : MulAut W) ∈ stabilizer := by
    have hcomm : Commute (j : MulAut W) (x : MulAut W) := by
      have hh := congrArg Subtype.val hx
      change (j : MulAut W) * (x : MulAut W) * (j : MulAut W)⁻¹ = (x : MulAut W) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hnorm : Subgroup.zpowers (x : MulAut W) ≤
        Subgroup.normalizer (Subgroup.zpowers (j : MulAut W) : Set (MulAut W)) := by
      apply le_trans _ (Subgroup.centralizer_le_normalizer _)
      apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_centralizer_iff]
      intro element helement
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp helement
      exact (hcomm.zpow_left n).eq
    have hinvariant := commutatorAction_isInvariant_of_normalizing_actor (V := W)
      (Subgroup.zpowers (x : MulAut W)) (Subgroup.zpowers (j : MulAut W)) hnorm
    have heq := commutatorAction_zpowers_eq_of_full_three J K hDcard hKcard hKfull hKJ
      (j : MulAut W) j.property (fun heq => hjne (Subtype.ext heq))
    rw [heq] at hinvariant
    intro point
    exact hinvariant.invariant ⟨x, Subgroup.mem_zpowers (x : MulAut W)⟩ point
  have hFstable : F ≤ stabilizer := by
    intro element helement
    have involutive (j : J) : Function.Involutive (action j) := by
      intro x
      change (action j * action j) x = x
      rw [← map_mul, ← pow_two, square j, map_one]
      rfl
    have hcommAction : Commute (action a) (action b) := by
      change action a * action b = action b * action a
      rw [← map_mul, ← map_mul, hab.eq]
    obtain ⟨x, y, z, hx, hy, hz, heq⟩ :=
      MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card hFodd
        (action a) (action b) (involutive a) (involutive b) hcommAction ⟨element, helement⟩
    have hz' : action (a * b) z = z := by simpa only [map_mul] using hz
    have heq' := congrArg Subtype.val heq
    change element = (x : MulAut W) * (y : MulAut W) * (z : MulAut W) at heq'
    rw [heq']
    exact stabilizer.mul_mem (stabilizer.mul_mem (hfixed a hane x hx) (hfixed b hbne y hy))
      (hfixed (a * b) habne z hz')
  have hinvariant : IsInvariant F W D := ⟨fun actor => hFstable actor.property⟩
  exact quadratic_false_of_invariant_displacement F J hfull hgenerate hquadratic hinvariant
    (fun heq => by rw [heq] at hJcard; simp at hJcard)
