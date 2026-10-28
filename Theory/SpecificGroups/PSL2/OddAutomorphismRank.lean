module

public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank

/-!
# Two-rank of automorphisms of odd-field PSL₂

The actual projective semilinear action identifies Aut(PSL₂(K)) with
PGL₂(K) ⋊ Aut(K) when K has odd cardinality greater than three. The kernel
of the field projection is PGL₂(K), whose dihedral Sylow two-subgroups
give two-rank at most two. The cyclic field automorphism group adds at
most one to the rank. This accounts for arbitrary diagonal and field
automorphisms, as well as inner automorphisms.

Over a prime field the field factor is trivial, so the bound is two.
The existing prime-field theorem is transported to every field carrier
of prime cardinality by an actual coefficient-field isomorphism.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, proof of G.7.3(1), printed p.348
(PDF p.359). The semilinear identification and dihedral Sylow models
are proved in the imported Gorenstein–Walter development.
-/

public section

open scoped MatrixGroups
open GorensteinWalter Theory.GroupTheory

namespace Theory.PSL2

private instance finiteFieldAut (K : Type*) [Field K] [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun a : K ≃+* K => (a : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))

/-- Dihedral Sylow two-subgroups bound the two-rank of odd-field PGL₂. -/
theorem odd_pgl_two_rank (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : primeRank 2 (PGL2 K) ≤ 2 := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let P : Sylow 2 (PGL2 K) := Classical.choice inferInstance
  obtain ⟨n, _, ⟨eP⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK P
  rw [P.primeRank_eq, primeRank_equiv 2 eP]
  exact dihedral_rank_le_two n

/-- The cyclic coefficient group adds at most one to the PGL₂ rank bound. -/
theorem odd_pGammaL_two_rank (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : primeRank 2 (PGammaL2 K) ≤ 3 := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (PGammaL2 K) :=
    Finite.of_equiv (PGL2 K × (K ≃+* K)) SemidirectProduct.equivProd.symm
  let f : PGammaL2 K →* (K ≃+* K) := SemidirectProduct.rightHom
  let e : PGL2 K ≃* f.ker :=
    (MonoidHom.ofInjective SemidirectProduct.inl_injective).trans
      (MulEquiv.subgroupCongr SemidirectProduct.range_inl_eq_ker_rightHom)
  have hker : primeRank 2 f.ker ≤ 2 := by
    rw [← primeRank_equiv 2 e]
    exact odd_pgl_two_rank K hK
  let : IsCyclic (K ≃+* K) := finiteField_ringAut_isCyclic_of_oddPrimePower K hK
  let P : Sylow 2 (K ≃+* K) := Classical.choice inferInstance
  have hfield : primeRank 2 (K ≃+* K) ≤ 1 :=
    P.primeRank_le_one_of_isCyclic inferInstance
  exact (primeRank_le_ker_add f).trans (by omega)

/-- The full automorphism group of odd-field PSL₂ has two-rank at most three. -/
theorem odd_automorphism_two_rank (K : Type*) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hlarge : 3 < Nat.card K) :
    primeRank 2 (MulAut PSL(2, K)) ≤ 3 := by
  obtain ⟨p, n, hp, hodd, hn, hcard⟩ := hK
  let : Fact p.Prime := ⟨hp⟩
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, n, hp, hodd, hn, hcard⟩
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let : Finite (PGammaL2 K) :=
    Finite.of_equiv (PGL2 K × (K ≃+* K)) SemidirectProduct.equivProd.symm
  let e : PGammaL2 K ≃* MulAut PSL(2, K) :=
    MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hK hlarge)
      ⟨pGammaL2ToMulAutPSL2_injective K hK hlarge,
        pGammaL2ToMulAutPSL2_surjective K hcard hK hlarge⟩
  rw [← primeRank_equiv 2 e]
  exact odd_pGammaL_two_rank K hK

/-- The sharper prime-field automorphism bound holds for any field carrier. -/
theorem prime_card_automorphism_two_rank (K : Type*) [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime] (hcard : Nat.card K = p) (hlarge : 3 < p) :
    primeRank 2 (MulAut PSL(2, K)) ≤ 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let eF : K ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, hcard, ZMod.card])
  rw [primeRank_equiv 2 (MulAut.congr (psl2RingEquiv eF))]
  exact primeField_automorphism_two_rank hlarge

end Theory.PSL2
