module

public import Theory.Representation.GeneralLinearNatural
public import Theory.Representation.SolvableDimension
public import Mathlib.GroupTheory.Nilpotent

/-!
# Absolute irreducibility of nonabelian odd prime-groups in degree three

A faithful, completely reducible degree-three representation of a nonabelian
solvable group of odd order is irreducible over an algebraically closed field.
Indeed, if it were reducible, each irreducible constituent would have dimension
less than three. Degree divisibility makes this dimension odd, hence one.
The constituents span by complete reducibility, so their scalar actions force
all operators to commute, contradicting faithfulness.

Applying this argument after extension to an algebraic closure proves absolute
irreducibility for nonabelian odd prime-subgroups of GL₃ in cross characteristic.
This is the irreducibility step in Aschbacher–Smith, Lemma A.3.21(c),
printed pp. 55–56 of `refs/quasithin.pdf`.
-/

public section

open scoped TensorProduct
namespace Representation

private theorem rankThree_atoms_span
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) [IsAtomistic (Subrepresentation ρ)] :
    (⨆ N : {N : Subrepresentation ρ // IsAtom N}, N.val.toSubmodule) = ⊤ := by
  let S : Submodule F V := ⨆ N : {N : Subrepresentation ρ // IsAtom N}, N.val.toSubmodule
  have hstable (g : G) : Submodule.map (ρ g) S ≤ S := by
    dsimp [S]
    rw [Submodule.map_iSup]
    apply iSup_le
    intro N
    apply le_trans _ (le_iSup _ N)
    rw [Submodule.map_le_iff_le_comap]
    exact N.val.apply_mem_toSubmodule g
  let T : Subrepresentation ρ :=
    ⟨S, fun g v hv => hstable g (Submodule.mem_map_of_mem hv)⟩
  have htop : (⊤ : Subrepresentation ρ) ≤ T := by
    rw [← sSup_atoms_eq_top]
    apply sSup_le
    intro N hN
    exact le_iSup (fun N : {N : Subrepresentation ρ // IsAtom N} => N.val.toSubmodule) ⟨N, hN⟩
  exact congrArg Subrepresentation.toSubmodule (top_le_iff.mp htop)

/-- A faithful completely reducible degree-three action of a nonabelian solvable
odd-order group is irreducible over an algebraically closed field. -/
theorem isIrreducible_of_finrank_eq_three_of_odd_card
    {F G V : Type*} [Field F] [IsAlgClosed F] [Group G] [Finite G]
    [Group.IsSolvable G] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hρ : ρ.IsCompletelyReducible)
    (hfaith : Function.Injective ρ) (hdim : Module.finrank F V = 3)
    (hodd : Odd (Nat.card G)) (hnonab : ¬ IsMulCommutative G) :
    IsIrreducible ρ := by
  classical
  let : IsSemisimpleModule (MonoidAlgebra F G) ρ.asModule := hρ
  let : IsAtomistic (Subrepresentation ρ) :=
    OrderIso.isAtomistic_of_isAtomistic
      Subrepresentation.subrepresentationSubmoduleOrderIso.symm inferInstance
  by_contra hirr
  have hdim_one (N : Subrepresentation ρ) (hN : IsAtom N) :
      Module.finrank F N.toSubmodule = 1 := by
    let : IsIrreducible N.toRepresentation := (Subrepresentation.irreducible_iff_isAtom N).2 hN
    let : IsAbsolutelyIrreducible N.toRepresentation :=
      (isAbsolutelyIrreducible_iff_surjective N.toRepresentation).2
        (surjective_of_jacobson_density_surjective_rep N.toRepresentation
          (jacobson_density_surjective_isAlgClosed_rep N.toRepresentation))
    have hdiv := lemma_2_3 N.toRepresentation
    have hlt : Module.finrank F N.toSubmodule < 3 := by
      rw [← hdim]
      apply Submodule.finrank_lt
      intro heq
      have hNtop : N = ⊤ := Subrepresentation.toSubmodule_injective heq
      exact hirr (isSimpleOrder_iff_isAtom_top.2 (hNtop ▸ hN))
    have ho := hodd.of_dvd_nat hdiv
    obtain ⟨k, hk⟩ := ho
    omega
  apply hnonab
  refine ⟨⟨fun a b => hfaith ?_⟩⟩
  rw [map_mul, map_mul]
  apply LinearMap.ext
  intro v
  have heq : (⨆ N : {N : Subrepresentation ρ // IsAtom N}, N.val.toSubmodule) ≤
      LinearMap.ker (ρ a * ρ b - ρ b * ρ a) := by
    apply iSup_le
    intro N
    obtain ⟨x, hx, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (hdim_one N.val N.property) (N.val.toRepresentation a)
    obtain ⟨y, hy, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
      (hdim_one N.val N.property) (N.val.toRepresentation b)
    intro w hw
    have hc : (N.val.toRepresentation a * N.val.toRepresentation b) =
        (N.val.toRepresentation b * N.val.toRepresentation a) := by
      rw [hx, hy]
      simp [smul_smul, mul_comm]
    have hc' := congrArg Subtype.val (DFunLike.congr_fun hc ⟨w, hw⟩)
    exact LinearMap.mem_ker.mpr (sub_eq_zero.mpr hc')
  rw [rankThree_atoms_span ρ] at heq
  exact sub_eq_zero.mp (LinearMap.mem_ker.mp (heq (Submodule.mem_top : v ∈ (⊤ : Submodule F V))))

/-- A nonabelian odd prime-group in GL₃ acts absolutely irreducibly in cross
characteristic. -/
theorem generalLinearNatural_three_isAbsolutelyIrreducible_of_isPGroup
    {F : Type*} [Field F] [Finite F] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    [CharP F p] (hqodd : Odd q) (hqp : q ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup q Q)
    (hnonab : ¬ IsMulCommutative Q) :
    IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype) := by
  let ρ := (generalLinearNatural (F := F) 3).comp Q.subtype
  let K := AlgebraicClosure F
  let σ := extendScalars K ρ
  let : Group.IsNilpotent Q := hQ.isNilpotent
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  have hchar : ringChar K = 0 ∨
      (Nat.Prime (ringChar K) ∧ Nat.Coprime (ringChar K) (Nat.card Q)) := by
    right
    rw [ringChar.eq K p, hn]
    exact ⟨Fact.out, ((Nat.coprime_primes Fact.out Fact.out).2 hqp.symm).pow_right n⟩
  refine ⟨isIrreducible_of_finrank_eq_three_of_odd_card σ
    (isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime σ hchar) ?_ ?_ ?_ hnonab⟩
  · exact (extendScalars_faithful_iff K ρ).1
      ((generalLinearNatural_injective 3).comp Subtype.val_injective)
  · change Module.finrank K (K ⊗[F] (Fin 3 → F)) = 3
    rw [Module.finrank_baseChange]
    simp
  · rw [hn]
    exact hqodd.pow

end Representation
