module

public import Theory.GroupTheory.PGroup.PrimeNormalAbelian
public import Theory.Representation.ThreeGroupWeightIndex
public import Theory.Representation.CharacterWeightLines
public import Theory.Representation.AbelianWeightNormalizerSolvable
public import Theory.Representation.AbsolutelyIrreducible

/-!
# An abelian weight base for nonabelian three-groups in GL₃

A finite nonabelian three-group in cross characteristic has a normal abelian
subgroup of index three whose ambient linear centralizer is abelian. Choose
a maximal normal abelian subgroup, which is self-centralizing in the group.
Its quotient acts faithfully on at most three character weights, hence has
order three. There are exactly three weights, all lines; centralizing linear
operators commute on these lines and therefore on their span.

Scalar extension to an algebraic closure preserves faithfulness and dimension.
The proof does not need irreducibility, and the last theorem retains the
absolutely irreducible interface used by the matrix-group application.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.3.21(c), printed pp. 55–56.
-/

public section

open scoped TensorProduct
namespace Representation

private theorem characterWeightSpace_comp_surjective
    {E K H V : Type*} [Field E] [Group K] [Group H]
    [AddCommGroup V] [Module E V]
    (sigma : Representation E H V) (f : K →* H) (hf : Function.Surjective f)
    (chi : H →* Eˣ) :
    characterWeightSpace (sigma.comp f) (chi.comp f) = sigma.characterWeightSpace chi := by
  ext v
  simp only [characterWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  change (∀ k, sigma (f k) v = (chi (f k) : E) • v) ↔
    (∀ h, sigma h v = (chi h : E) • v)
  constructor
  · intro h k
    obtain ⟨x, rfl⟩ := hf k
    exact h x
  · intro h k
    exact h (f k)

/-- A faithful degree-three representation gives an abelian index-three base
whose centralizer in the ambient group is abelian. -/
theorem exists_normal_abelian_index_three_ambient_centralizer
    {E G V : Type*} [Field E] [IsAlgClosed E] [Group G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (rho : Representation E G V) (hrho : Function.Injective rho)
    (hdim : Module.finrank E V = 3)
    (Q : Subgroup G) [Finite Q] (hQ : IsPGroup 3 Q)
    (hn : ¬ IsMulCommutative Q) (horder : (Nat.card Q : E) ≠ 0) :
    ∃ A : Subgroup Q, A.Normal ∧ IsMulCommutative A ∧ A.index = 3 ∧
      IsMulCommutative (Subgroup.centralizer ((A.map Q.subtype : Subgroup G) : Set G)) := by
  obtain ⟨A, hAn, hAc, hCA⟩ := hQ.exists_normal_abelian_selfCentralizing
  let := hAn
  let := hAc
  have horderA : (Nat.card A : E) ≠ 0 := by
    intro hz
    apply horder
    rw [← A.card_mul_index, Nat.cast_mul, hz, zero_mul]
  obtain ⟨hi, hc⟩ := threeGroup_abelian_selfCentralizing_index_and_weights
    (rho.comp Q.subtype) (hrho.comp Subtype.val_injective) hQ hn hdim.le A hCA horderA
  have hlines (chi : CharacterWeight ((rho.comp Q.subtype).comp A.subtype)) :
      Module.finrank E (characterWeightSpace ((rho.comp Q.subtype).comp A.subtype) chi.val) = 1 :=
    characterWeight_finrank_one_of_card_eq_finrank _ horderA (hc.trans hdim.symm) chi
  refine ⟨A, hAn, hAc, hi, ?_⟩
  let B : Subgroup G := A.map Q.subtype
  have horderB : (Nat.card B : E) ≠ 0 := by
    dsimp [B]
    rwa [Subgroup.card_map_of_injective Q.subtype_injective]
  apply centralizer_isMulCommutative_of_characterWeight_finrank_one rho B hrho horderB
  intro chi
  let f : A →* B := Q.subtype.subgroupMap A
  have heq : characterWeightSpace ((rho.comp Q.subtype).comp A.subtype) (chi.val.comp f) =
      characterWeightSpace (rho.comp B.subtype) chi.val :=
    characterWeightSpace_comp_surjective (rho.comp B.subtype) f
      (Q.subtype.subgroupMap_surjective A) chi.val
  let chiA : CharacterWeight ((rho.comp Q.subtype).comp A.subtype) :=
    ⟨chi.val.comp f, by rw [heq]; exact chi.property⟩
  have hline := hlines chiA
  change Module.finrank E (characterWeightSpace ((rho.comp Q.subtype).comp A.subtype)
    (chi.val.comp f)) = 1 at hline
  rwa [heq] at hline

/-- Every nonabelian three-subgroup of GL₃ in cross characteristic has an
abelian normal index-three subgroup with abelian ambient centralizer. -/
theorem generalLinear_threeGroup_exists_normal_abelian_index_three
    {F : Type*} [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup 3 Q)
    (hn : ¬ IsMulCommutative Q) :
    ∃ A : Subgroup Q, A.Normal ∧ IsMulCommutative A ∧ A.index = 3 ∧
      IsMulCommutative (Subgroup.centralizer
        ((A.map Q.subtype : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F))) := by
  let E := AlgebraicClosure F
  let rho := (generalLinearNatural (F := F) 3).extendScalars E
  have hrho : Function.Injective rho :=
    (extendScalars_faithful_iff E _).mp (generalLinearNatural_injective 3)
  have hdim : Module.finrank E (E ⊗[F] (Fin 3 → F)) = 3 := by
    rw [Module.finrank_baseChange, Module.finrank_pi, Fintype.card_fin]
  have h3 : (3 : F) ≠ 0 := by
    change (↑(3 : ℕ) : F) ≠ 0
    rw [ne_eq, CharP.cast_eq_zero_iff F p]
    intro hdiv
    exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp hdiv).symm
  have horderF : (Nat.card Q : F) ≠ 0 := by
    obtain ⟨n, hncard⟩ := hQ.exists_card_eq
    rw [hncard, Nat.cast_pow]
    exact pow_ne_zero n h3
  have horder : (Nat.card Q : E) ≠ 0 := by
    intro hz
    apply horderF
    apply (algebraMap F E).injective
    simpa using hz
  exact exists_normal_abelian_index_three_ambient_centralizer rho hrho hdim Q hQ hn horder

/-- The structural weight-base witness for the absolutely irreducible case. -/
theorem generalLinear_absolutelyIrreducible_threeGroup_weightBase
    {F : Type*} [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] (hp : 3 ≠ p)
    (Q : Subgroup (GL (Fin 3) F)) (hQ : IsPGroup 3 Q)
    (hn : ¬ IsMulCommutative Q)
    (_hirr : IsAbsolutelyIrreducible ((generalLinearNatural (F := F) 3).comp Q.subtype)) :
    ∃ A : Subgroup Q, A.Normal ∧ IsMulCommutative A ∧ A.index = 3 ∧
      IsMulCommutative (Subgroup.centralizer
        ((A.map Q.subtype : Subgroup (GL (Fin 3) F)) : Set (GL (Fin 3) F))) :=
  generalLinear_threeGroup_exists_normal_abelian_index_three p hp Q hQ hn
end Representation
