module
public import Theory.SpecificGroups.SymplecticFour.SevenNormalizer
public import Theory.SpecificGroups.SL2.ProjectiveBorelFrobenius
public import Theory.Representation.AbelianFrobeniusDegree
public import Theory.Representation.SymplecticNatural
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions

/-!
# Excluding odd-prime PSL2 subgroups from symplectic four-space

The genuine projective Borel acts freely on its additive unipotent kernel.
Its character-weight orbit bounds its complement order by the coefficient-field
representation degree, which is four. For a prime parameter greater than five
this leaves only seven. The actual exceptional isomorphism with PSL3(2) supplies
a seven-element conjugate to its square, excluded by the symplectic spectrum.

This proves the odd-prime exclusion in Aschbacher--Smith E.2.7, printed p.220.
It uses neither irreducibility nor a subgroup classification, and the ambient
field may be any field of characteristic two.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour
open Matrix.ProjectiveSpecialLinearGroup
variable {F : Type*} [Field F] [CharP F 2]

/-- The actual odd PSL2 Borel forces its complement to fit into four dimensions. -/
theorem odd_psl2_borel_bound {K : Type*} [Field K] [Finite K]
    (hq : Odd (Nat.card K)) (j : PSL(2,K) →* Sp F) (hj : Function.Injective j) :
    (Nat.card K - 1) / 2 ≤ 4 := by
  let rho := (Representation.symplecticNatural (k := F) 2).comp j
  have hfaith : Function.Injective rho := by
    intro x y h
    apply hj
    apply Subtype.ext
    ext i k
    have hv := congrArg (fun f : Module.End F ((Fin 2 ⊕ Fin 2) → F) =>
      f (Pi.single k 1) i) h
    simpa [rho, Representation.symplecticNatural_apply, Matrix.mulVec_single] using hv
  have ho : (Nat.card (OddBorel.kernel K) : F) ≠ 0 := by
    rw [OddBorel.card_kernel,
      natCast_eq_one_of_odd_of_two_eq_zero hq (CharP.cast_eq_zero F 2)]
    exact one_ne_zero
  have hb := Representation.card_le_finrank_of_fixedPointFree_normalizer_of_field
    rho (OddBorel.kernel K) (OddBorel.complement K) hfaith ho
    (OddBorel.complement_normalizes K) (OddBorel.fixedPointFree K)
  rw [OddBorel.card_complement] at hb
  have hd : 2 ∣ Nat.card K - 1 := by obtain ⟨n, hn⟩ := hq; exact ⟨n, by omega⟩
  rw [Nat.gcd_eq_right_iff_dvd.mpr hd] at hb
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_sum,
    Fintype.card_fin, mul_one] using hb

/-- Prime odd-field projective rank-one groups beyond A5 cannot embed in
symplectic four-space in characteristic two. -/
theorem odd_prime_psl2_not_injective {K : Type*} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) (hK : Nat.card K = p)
    (j : PSL(2,K) →* Sp F) : ¬ Function.Injective j := by
  intro hj
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hb := odd_psl2_borel_bound (hK.symm ▸ hodd) j hj
  rw [hK] at hb
  have hp7 : p = 7 := by
    have hple : p ≤ 10 := by omega
    have hp6 : p ≠ 6 := by rintro rfl; norm_num at hp
    have hp8 : p ≠ 8 := by rintro rfl; norm_num at hp
    have hp9 : p ≠ 9 := by rintro rfl; norm_num at hp
    have hp10 : p ≠ 10 := by rintro rfl; norm_num at hp
    omega
  have hK7 : Nat.card K = 7 := hK.trans hp7
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : Fintype K := Fintype.ofFinite K
  let eK : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hK7)
  let e : PSL(2,K) ≃* Matrix.PSL3Two.PSL := (Atlas.fieldEquivPSL 2 eK).trans
    Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two
  let f := j.comp e.symm.toMonoidHom
  have hf : Function.Injective f := hj.comp e.symm.injective
  obtain ⟨a,b,ha,han,hab⟩ := Matrix.PSL3Two.exists_seven_conjugate_square
  apply SevenNormalizer.seven_not_conjugate_square (f a) (f b)
  · rw [← map_pow,ha,map_one]
  · exact fun h => han (hf (h.trans f.map_one.symm))
  · simpa only [map_mul,map_inv,map_pow] using congrArg f hab

end Theory.SpecificGroups.SymplecticFour
