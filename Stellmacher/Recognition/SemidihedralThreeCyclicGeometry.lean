module

public import Stellmacher.Recognition.SemidihedralThreePrincipalCharacters
public import Theory.GroupTheory.PrimeOrderSylowArithmetic
public import Theory.Character.PrimeDegree
public import Theory.Character.PrimeDegreeAutomizer
public import Theory.Character.PrimeDegreeCentralizer

/-!
# Prime-order Sylow geometry for the characteristic-three branch

The retained principal characters and the Schur order bounds give Sylow
subgroups of order eleven or thirteen. The degree-prime row is afforded by
a faithful rational-valued complex representation and vanishes on all
prime-singular elements. Semidihedral involution fusion transports the
local centralizer bound and the character values, proving that the two
prime-order Sylow centralizers have odd order.

The prime-degree character theorems then give self-centralization from
faithfulness and rationality, and odd automizers from restriction to a
dihedral subgroup and the involution values `3` and `-3`. Both case-specific
conclusions retain the original semidihedral N₂ hypotheses.

Source: Alperin--Brauer--Gorenstein, III.8 Lemma 4 and Proposition 5,
article pp.116--117. The initial case adapters were adapted from the saved
SemidihedralCyclic/DraftSetup.lean development.
-/

namespace Stellmacher.Recognition
open ABG
section
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

private theorem involutions_conjugate
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  obtain ⟨r, _, _, hc⟩ := hclass
  obtain ⟨i, hi⟩ := hc x hx
  obtain ⟨j, hj⟩ := hc y hy
  exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)

private def centralizerEquiv (e : G ≃* G) (x : G) :
    Subgroup.centralizer {x} ≃* Subgroup.centralizer {e x} where
  toFun a := ⟨e a, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp a.property))⟩
  invFun a := ⟨e.symm a, Subgroup.mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv a := Subtype.ext (e.apply_symm_apply a)
  map_mul' a b := Subtype.ext (map_mul e (a : G) (b : G))

/-- The local order bound transports to every involution by fusion. -/
public theorem semidihedral_involutionCentralizer_card_dvd
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) {x : G}
    (hx : orderOf x = 2) {n : ℕ}
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ n)
    (t : G) (ht : orderOf t = 2) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) ∣ n := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (involutions_conjugate S hS hx ht)
  have he : (MulAut.conj g) x = t := hg
  have hc := Nat.card_congr (centralizerEquiv (MulAut.conj g) x).toEquiv
  rw [he] at hc
  rwa [← hc]

/-- A prime-order Sylow has odd centralizer when its prime is absent
from the common involution-centralizer order bound. -/
public theorem semidihedral_prime_sylow_centralizer_odd
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) {x : G}
    (hx : orderOf x = 2) {n p : ℕ}
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ n)
    (hp : ¬ p ∣ n) (P : Sylow p G) (hP : Nat.card P = p) :
    Odd (Nat.card (Subgroup.centralizer (P : Set G))) := by
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  apply P.not_two_dvd_centralizer_card hP
  intro t ht hd
  exact hp (hd.trans (semidihedral_involutionCentralizer_card_dvd S hS hx hlocal t ht))

end

namespace SemidihedralThreePrincipalCharacters
variable {G : Type*} [Group G] [Finite G] {x : G} {T : Subgroup G}
  (c : SemidihedralThreePrincipalCharacters G x T)

/-- Extract the first order formula using the degree of the actual first row. -/
public theorem case_one_order (hf : c.degree 0 = 11) :
    Nat.card G = 7920 * (Nat.card (threePrincipalCoreCentralizer x T) *
      (threePrincipalCoreCentralizer x T).index ^ 3) := by
  rcases c.alternatives with h | h
  · exact h.2.2.2.2.2
  · omega

/-- Extract the second order formula using the degree of the actual second row. -/
public theorem case_two_order (hf : c.degree 1 = 13) :
    Nat.card G = 5616 * (Nat.card (threePrincipalCoreCentralizer x T) *
      (threePrincipalCoreCentralizer x T).index ^ 3) := by
  rcases c.alternatives with h | h
  · omega
  · exact h.2.2.2.2.2

/-- In Case I the degree-eleven prime occurs exactly once in the group order. -/
public theorem case_one_sylow_card (hf : c.degree 0 = 11)
    (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) (P : Sylow 11 G) :
    Nat.card P = 11 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  apply P.card_eq_prime_of_dvd_of_not_sq_dvd
  · rw [c.case_one_order hf]
    exact (by norm_num : 11 ∣ 7920).trans (dvd_mul_right _ _)
  · intro h
    have := h.trans hbound
    norm_num at this

/-- In Case II the degree-thirteen prime occurs exactly once in the group order. -/
public theorem case_two_sylow_card (hf : c.degree 1 = 13)
    (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) (P : Sylow 13 G) :
    Nat.card P = 13 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  apply P.card_eq_prime_of_dvd_of_not_sq_dvd
  · rw [c.case_two_order hf]
    exact (by norm_num : 13 ∣ 5616).trans (dvd_mul_right _ _)
  · intro h
    have := h.trans hbound
    norm_num at this

/-- The first Case I row is a faithful rational-valued degree-eleven character. -/
public theorem case_one_faithful_rational [IsSimpleGroup G] (hf : c.degree 0 = 11) :
    ∃ ρ : Representation ℂ G (Fin 11 → ℂ),
      ofConjClassFunction (c.toThreePrincipalData.χ 1) = ρ.character ∧
      Function.Injective ρ ∧ (∀ g : G, ∃ q : ℚ, ρ.character g = (q : ℂ)) := by
  have hd : c.toThreePrincipalData.χ 1 (ConjClasses.mk 1) = 11 := by
    simpa [ThreePrincipalData.χ, hf] using c.degree_value 1
  exact (c.toThreePrincipalData.irreducible 1).exists_faithful_rational_prime_degree
    (by decide) hd (c.rational 1)

/-- The second Case II row is a faithful rational-valued degree-thirteen character. -/
public theorem case_two_faithful_rational [IsSimpleGroup G] (hf : c.degree 1 = 13) :
    ∃ ρ : Representation ℂ G (Fin 13 → ℂ),
      ofConjClassFunction (c.toThreePrincipalData.χ 2) = ρ.character ∧
      Function.Injective ρ ∧ (∀ g : G, ∃ q : ℚ, ρ.character g = (q : ℂ)) := by
  have hd : c.toThreePrincipalData.χ 2 (ConjClasses.mk 1) = 13 := by
    simpa [ThreePrincipalData.χ, hf] using c.degree_value 2
  exact (c.toThreePrincipalData.irreducible 2).exists_faithful_rational_prime_degree
    (by decide) hd (c.rational 2)

/-- The degree-eleven row vanishes on all eleven-singular elements. -/
public theorem case_one_vanishing (hf : c.degree 0 = 11)
    (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11)
    (g : G) (hg : 11 ∣ orderOf g) :
    c.toThreePrincipalData.χ 1 (ConjClasses.mk g) = 0 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P : Sylow 11 G := Classical.choice inferInstance
  apply (c.toThreePrincipalData.irreducible 1).prime_degree_vanishing P
    (c.case_one_sylow_card hf hbound P) _ g hg
  simpa [ThreePrincipalData.χ, hf] using c.degree_value 1

/-- The degree-thirteen row vanishes on all thirteen-singular elements. -/
public theorem case_two_vanishing (hf : c.degree 1 = 13)
    (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13)
    (g : G) (hg : 13 ∣ orderOf g) :
    c.toThreePrincipalData.χ 2 (ConjClasses.mk g) = 0 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let P : Sylow 13 G := Classical.choice inferInstance
  apply (c.toThreePrincipalData.irreducible 2).prime_degree_vanishing P
    (c.case_two_sylow_card hf hbound P) _ g hg
  simpa [ThreePrincipalData.χ, hf] using c.degree_value 2

/-- Fusion extends the two distinguished character values to all involutions. -/
public theorem first_two_values_on_all_involutions
    [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hx : orderOf x = 2)
    (t : G) (ht : orderOf t = 2) :
    c.toThreePrincipalData.χ 1 (ConjClasses.mk t) = 3 ∧
      c.toThreePrincipalData.χ 2 (ConjClasses.mk t) = -3 := by
  have he : ConjClasses.mk x = ConjClasses.mk t :=
    ConjClasses.mk_eq_mk_iff_isConj.mpr (involutions_conjugate S hS hx ht)
  rw [← he]
  exact c.first_two_involution_values

/-- The Sylow-eleven centralizer in Case I has odd order. -/
public theorem case_one_centralizer_odd [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hx : orderOf x = 2)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 0 = 11)
    (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) (P : Sylow 11 G) :
    Odd (Nat.card (Subgroup.centralizer (P : Set G))) :=
  semidihedral_prime_sylow_centralizer_odd S hS hx hlocal (by norm_num) P
    (c.case_one_sylow_card hf hbound P)

/-- The Sylow-thirteen centralizer in Case II has odd order. -/
public theorem case_two_centralizer_odd [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hx : orderOf x = 2)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 1 = 13)
    (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) (P : Sylow 13 G) :
    Odd (Nat.card (Subgroup.centralizer (P : Set G))) :=
  semidihedral_prime_sylow_centralizer_odd S hS hx hlocal (by norm_num) P
    (c.case_two_sylow_card hf hbound P)

/-- In Case I every Sylow-eleven subgroup is self-centralizing and has odd
 automizer, using the actual rational irreducible row of degree eleven. -/
public theorem case_one_sylow_geometry [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (_hN : IsNTwoGroup G)
    (hx : orderOf x = 2) (_hT : IsElementaryAbelian 2 T)
    (_hTcard : Nat.card T = 4) (_hxT : x ∈ T)
    (_hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 0 = 11)
    (hbound : Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) (P : Sylow 11 G) :
    Subgroup.centralizer (P : Set G) = (P : Subgroup G) ∧
      Odd (ABG.automizerIndex (P : Subgroup G)) := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hP := c.case_one_sylow_card hf hbound P
  have hodd := c.case_one_centralizer_odd S hS hx hlocal hf hbound P
  obtain ⟨ρ, hρ, hfaith, hrat⟩ := c.case_one_faithful_rational hf
  have hv : ∀ g : G, 11 ∣ orderOf g → ρ.character g = 0 := by
    intro g hg
    rw [← hρ]
    exact c.case_one_vanishing hf hbound g hg
  constructor
  · exact ρ.centralizer_sylow_eq_of_faithful_rational_prime_degree
      P hP hodd hfaith hrat hv
  · apply Representation.odd_automizer_of_prime_degree (by decide) P hP hodd ρ hv
    intro t ht
    left
    rw [← hρ]
    exact (c.first_two_values_on_all_involutions S hS hx t ht).1

/-- In Case II every Sylow-thirteen subgroup is self-centralizing and has odd
 automizer, using the actual rational irreducible row of degree thirteen. -/
public theorem case_two_sylow_geometry [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (_hN : IsNTwoGroup G)
    (hx : orderOf x = 2) (_hT : IsElementaryAbelian 2 T)
    (_hTcard : Nat.card T = 4) (_hxT : x ∈ T)
    (_hA : (threePrincipalCoreCentralizer x T).index ≠ 1)
    (hlocal : Nat.card (Subgroup.centralizer ({x} : Set G)) ∣ 720)
    (hf : c.degree 1 = 13)
    (hbound : Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13) (P : Sylow 13 G) :
    Subgroup.centralizer (P : Set G) = (P : Subgroup G) ∧
      Odd (ABG.automizerIndex (P : Subgroup G)) := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hP := c.case_two_sylow_card hf hbound P
  have hodd := c.case_two_centralizer_odd S hS hx hlocal hf hbound P
  obtain ⟨ρ, hρ, hfaith, hrat⟩ := c.case_two_faithful_rational hf
  have hv : ∀ g : G, 13 ∣ orderOf g → ρ.character g = 0 := by
    intro g hg
    rw [← hρ]
    exact c.case_two_vanishing hf hbound g hg
  constructor
  · exact ρ.centralizer_sylow_eq_of_faithful_rational_prime_degree
      P hP hodd hfaith hrat hv
  · apply Representation.odd_automizer_of_prime_degree (by decide) P hP hodd ρ hv
    intro t ht
    right
    rw [← hρ]
    exact (c.first_two_values_on_all_involutions S hS hx t ht).2

end SemidihedralThreePrincipalCharacters
end Stellmacher.Recognition
