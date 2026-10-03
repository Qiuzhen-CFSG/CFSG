module
public import Theory.FieldTheory.OddQuadraticRestriction
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Lifting a prescribed odd coefficient subgroup to the quadratic field

For a prime p and nonzero n, an odd-order subgroup D of the actual
coefficient automorphisms of GF(p^n) has a lift A inside the automorphisms
of GF(p^(2n)). The subgroup A is chosen before any identification of the
q-Frobenius fixed field with GF(p^n). For every supplied identification b,
there is an injective restriction map r with image exactly D and with the
explicit compatibility equation on the original fixed-field elements.
The prime p may be two, and n may be one.

Ring automorphisms of a finite field are exactly its algebra automorphisms
over the prime field. Their groups are therefore cyclic of orders n and
2n. Choose A as the kernel of the |D|-power homomorphism; cyclicity gives
|A|=|D|. The existing odd quadratic restriction theorem applies for each b.
Both its image and D lie in the base-field |D|-power kernel and have that
kernel's order, so both equal it. This proves equality of the actual
coefficient subgroup, without replacing the supplied coordinate map.

This is the coefficient-lifting step in Alperin--Brauer--Gorenstein II.3
Proposition 3, article pages 27--28. It permits choosing the equivariant
SU2/SL2 coordinates after the quadratic coefficient subgroup while retaining
the original projective complement's coefficient image.
-/

namespace GaloisField

private theorem ringAut_facts (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    IsCyclic (GaloisField p n ≃+* GaloisField p n) ∧
      Nat.card (GaloisField p n ≃+* GaloisField p n) = n := by
  let F := GaloisField p n
  let e : (F ≃+* F) ≃* (F ≃ₐ[ZMod p] F) := {
    toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
      intro x
      have hh : σ.toRingHom.comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun hh x)
    invFun σ := σ.toRingEquiv
    left_inv σ := by ext x; rfl
    right_inv σ := by ext x; rfl
    map_mul' σ τ := by ext x; rfl }
  refine ⟨e.isCyclic.mpr inferInstance, ?_⟩
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
  exact GaloisField.finrank p hn

/-- The ring automorphism group of GF(p^n) has order n. -/
public theorem card_ringAut (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (GaloisField p n ≃+* GaloisField p n) = n :=
  (ringAut_facts p n hn).2

/-- A quadratic lift chosen before the fixed-field coordinates restricts onto
exactly the prescribed odd coefficient subgroup under every such coordinate map. -/
public theorem exists_odd_quadratic_coefficient_lift
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (D : Subgroup (GaloisField p n ≃+* GaloisField p n))
    (hD : Odd (Nat.card D)) :
    ∃ A : Subgroup (GaloisField p (2*n) ≃+* GaloisField p (2*n)),
      Odd (Nat.card A) ∧
      ∀ b : (FixedBy.subfield (GaloisField p (2*n))
        (iterateFrobeniusEquiv (GaloisField p (2*n)) p n)) ≃+* GaloisField p n,
        ∃ r : A →* (GaloisField p n ≃+* GaloisField p n),
          Function.Injective r ∧ r.range = D ∧
          ∀ (σ : A) (x : FixedBy.subfield (GaloisField p (2*n))
            (iterateFrobeniusEquiv (GaloisField p (2*n)) p n)),
            σ.val x.val = (b.symm (r σ (b x))).val := by
  classical
  obtain ⟨hcF,hcardF⟩ := ringAut_facts p n hn
  obtain ⟨hcE,hcardE⟩ := ringAut_facts p (2*n) (Nat.mul_ne_zero (by decide) hn)
  let : IsCyclic (GaloisField p n ≃+* GaloisField p n) := hcF
  let : IsCyclic (GaloisField p (2*n) ≃+* GaloisField p (2*n)) := hcE
  let : CommGroup (GaloisField p n ≃+* GaloisField p n) := IsCyclic.commGroup
  let : CommGroup (GaloisField p (2*n) ≃+* GaloisField p (2*n)) := IsCyclic.commGroup
  let : Finite (GaloisField p n ≃+* GaloisField p n) :=
    Finite.of_injective (fun σ => (σ : GaloisField p n → GaloisField p n)) DFunLike.coe_injective
  let : Finite (GaloisField p (2*n) ≃+* GaloisField p (2*n)) :=
    Finite.of_injective (fun σ => (σ : GaloisField p (2*n) → GaloisField p (2*n))) DFunLike.coe_injective
  have hd : Nat.card D ∣ n := by
    simpa only [hcardF] using D.card_subgroup_dvd_card
  let A := (powMonoidHom (Nat.card D) :
    (GaloisField p (2*n) ≃+* GaloisField p (2*n)) →*
      (GaloisField p (2*n) ≃+* GaloisField p (2*n))).ker
  have hAcard : Nat.card A = Nat.card D := by
    rw [IsCyclic.card_powMonoidHom_ker, hcardE]
    exact Nat.gcd_eq_right (dvd_mul_of_dvd_right hd 2)
  have hAodd : Odd (Nat.card A) := hAcard ▸ hD
  refine ⟨A,hAodd,?_⟩
  intro b
  obtain ⟨r,hr,hres⟩ := exists_injective_odd_quadratic_restriction p n hn A hAodd b
  refine ⟨r,hr,?_,hres⟩
  let C := (powMonoidHom (Nat.card D) :
    (GaloisField p n ≃+* GaloisField p n) →* (GaloisField p n ≃+* GaloisField p n)).ker
  have hCcard : Nat.card C = Nat.card D := by
    rw [IsCyclic.card_powMonoidHom_ker,hcardF]
    exact Nat.gcd_eq_right hd
  have hDC : D ≤ C := by
    intro σ hσ
    change σ ^ Nat.card D = 1
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨σ,hσ⟩ : D)))
  have hRC : r.range ≤ C := by
    rintro σ ⟨τ,rfl⟩
    change r τ ^ Nat.card D = 1
    rw [← map_pow,← hAcard,pow_card_eq_one',map_one]
  have hRcard : Nat.card r.range = Nat.card D := by
    exact (Nat.card_congr (Equiv.ofInjective r hr)).symm.trans hAcard
  exact (Subgroup.eq_of_le_of_card_ge hRC (hCcard.trans hRcard.symm).le).trans
    (Subgroup.eq_of_le_of_card_ge hDC hCcard.le).symm
end GaloisField
