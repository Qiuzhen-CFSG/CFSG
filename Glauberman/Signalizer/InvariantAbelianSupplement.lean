module
public import Glauberman.Signalizer.SolvableZJNormalizer
public import Theory.GroupAction.OddInvariantSylow
public import Glauberman.CharacteristicFunctor.Invariant

/-!
# An invariant abelian prime subgroup with a normalizer supplement

Let a finite two-group A act on a finite odd solvable group H. For a prime
q at least five dividing |H|, there is a nontrivial A-invariant abelian
q-subgroup Q whose normalizer supplements O_{q′}(H). The result uses the
actual supplied action and places Q in H itself.

Choose an A-invariant Sylow q-subgroup S using odd-order invariant Sylow
existence, and take Q=Z(J(S)) through the canonical ZJ characteristic
functor. Divisibility of |H| makes S nontrivial, and the functor preserves
nontriviality and containment in S. Its injective-map naturality applied
to each actor automorphism carries invariance of S to Q. The definition
of Z(J(S)) as the center of J(S) makes Q abelian. Finally the proved
solvable ZJ normalizer theorem gives O_{q′}(H) N_H(Q)=H, expressed as a join.

This is the full-Sylow ZJ choice used for the q≥5 branch of the binary
signalizer factorization argument in Kurzweil–Stellmacher, *The Theory of
Finite Groups*, §11.2. Its normalizer input is the ZJ version of 9.4.6,
proved in `Glauberman.Signalizer.SolvableZJNormalizer`; no signalizer family
assumptions are part of the present group-action statement.
-/

namespace Glauberman

/-- A nontrivial invariant abelian q-subgroup whose normalizer supplements the q′-core. -/
public theorem exists_invariant_abelian_prime_normalizer_supplement
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    [MulDistribMulAction A H] (hA : IsPGroup 2 A) (hodd : Odd (Nat.card H))
    (hsolv : Group.IsSolvable H) {q : ℕ} [Fact q.Prime]
    (hq : 5 ≤ q) (hdiv : q ∣ Nat.card H) :
    ∃ Q : Subgroup H, Q ≠ ⊥ ∧ IsPGroup q Q ∧ IsMulCommutative Q ∧
      IsInvariant A H Q ∧ pPrimeCore q H ⊔ Subgroup.normalizer (Q : Set H) = ⊤ := by
  obtain ⟨S, _, hSI⟩ := exists_invariant_sylow_le_of_isPGroup (p := q) hA hodd
    (⊥ : Subgroup H) IsPGroup.of_bot (isInvariant_of_characteristic (A := A) ⊥)
  let Q : Subgroup H := (zjCharacteristicFunctor q).K (S : Subgroup H)
  have hQne : Q ≠ ⊥ :=
    (zjCharacteristicFunctor q).K_nontrivial _ S.isPGroup' (S.ne_bot_of_dvd_card hdiv)
  have hQp : IsPGroup q Q := S.isPGroup'.to_le ((zjCharacteristicFunctor q).K_le _)
  have hQcomm : IsMulCommutative Q := by
    apply Subgroup.le_centralizer_iff_isMulCommutative.mp
    change centerIn (thompsonSubgroup (S : Subgroup H)) ≤
      Subgroup.centralizer (centerIn (thompsonSubgroup (S : Subgroup H)) : Set H)
    exact (show centerIn (thompsonSubgroup (S : Subgroup H)) ≤
      Subgroup.centralizer (thompsonSubgroup (S : Subgroup H) : Set H) from inf_le_right).trans
      (Subgroup.centralizer_le (show
        (centerIn (thompsonSubgroup (S : Subgroup H)) : Set H) ⊆
          (thompsonSubgroup (S : Subgroup H) : Set H) from inf_le_left))
  let _ : IsInvariant A H (S : Subgroup H) := hSI
  have hQI : IsInvariant A H Q := (zjCharacteristicFunctor q).isInvariant (S : Subgroup H)
  exact ⟨Q, hQne, hQp, hQcomm, hQI, solvable_oddPrime_normalizer_zj_supplement hq hsolv S⟩

end Glauberman
