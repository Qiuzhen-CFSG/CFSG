module
public import ABG.Recognition.ThreePairDegreeEquations
public import ABG.Recognition.ThreeDegreeArithmetic

/-!
# Wong's global degree alternatives and resolved restrictions

The involution-pair identities and the ordinary restriction congruence apply to
one shared catalog of seven genuine irreducible characters. Integer arithmetic
forces their signed degrees; positivity of actual character degrees then
resolves all four signs. This gives the positive degree vectors and the two
possible group orders, together with the Appendix restrictions on the roots of
the distinguished involution. The final existence theorem retains the original
induction, vanishing, and divisibility witnesses.

Source: Wong (1964), pp.99–101, equations (3)–(10), and Appendix p.106,
equation (12). No modular decomposition data are assumed.
-/

namespace ABG
open BenderGlauberman
noncomputable section

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
  (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
  (t : G) (ht : orderOf t = 2)
  (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
  (d : ThreeCharacterDecomposition (threeInducedGenerator t e))

include hS ht in
/-- The congruence and both polynomial equations refer to the first and sixth
signed degrees of the actual irreducibles in the induction identities. -/
public theorem threeInduced_global_degree_identities :
    let x : ℤ := d.signedDegree 0
    let y : ℤ := d.signedDegree 5
    8 ∣ x - 2 ∧
    (Nat.card G : ℤ) * (x - 2)^2 = 4608*x*(x+1) ∧
    y^2*(2*x-1)*(x-8) + 2*y*(x+1)*(x^2-16*x+4) - 16*x*(x+1)^2 = 0 :=
  ⟨threeInduced_signed_degree_congruence t ht e d,
    threeInduced_pair_degree_equations t e S hS ht d⟩

include hS ht in
/-- Wong's two signed degree vectors, for the same seven-character catalog. -/
public theorem threeInduced_signed_degree_alternatives :
    (d.signedDegree = ![10,11,10,10,-55,44,45] ∧ Nat.card G = 7920) ∨
    (d.signedDegree = ![26,27,26,26,-39,12,13] ∧ Nat.card G = 5616) := by
  obtain ⟨hcong, horder, hquad⟩ := threeInduced_global_degree_identities S hS t ht e d
  have hv := threeInduced_signed_degree_vector t ht e d
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  have h4 := congrFun hv 4
  have h6 := congrFun hv 6
  simp only [Matrix.cons_val] at h1 h2 h3 h4 h6
  exact three_seven_signed_degree_alternatives (Nat.card G) d.signedDegree
    (by omega) (by omega) (by omega) (by omega) (by omega) hcong hquad horder

omit [Finite G] [IsSimpleGroup G] in
private theorem degree_natAbs {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ) (i : Fin 7) :
    (d.signedDegree i).natAbs = d.degree i := by
  rcases d.degreeSign_unit i with h | h <;>
    simp [ThreeCharacterDecomposition.signedDegree, h]

omit [Finite G] [IsSimpleGroup G] in
private theorem degreeSign_of_pos {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ) (i : Fin 7)
    (h : 0 < d.signedDegree i) : d.degreeSign i = 1 := by
  rcases d.degreeSign_unit i with hs | hs
  · exact hs
  · simp [ThreeCharacterDecomposition.signedDegree, hs] at h
    omega

omit [Finite G] [IsSimpleGroup G] in
private theorem degreeSign_of_neg {Ψ : Fin 5 → ClassFunction G}
    (d : ThreeCharacterDecomposition Ψ) (i : Fin 7)
    (h : d.signedDegree i < 0) : d.degreeSign i = -1 := by
  rcases d.degreeSign_unit i with hs | hs
  · simp [ThreeCharacterDecomposition.signedDegree, hs] at h
    omega
  · exact hs

include hS ht in
/-- The four original signs are ε = 1, ε₁ = -1, ε₂ = ε₃ = 1. -/
public theorem threeInduced_signs : d.sign = ![1,-1,1,1] := by
  have hpos : 0 < d.signedDegree 0 ∧ d.signedDegree 4 < 0 ∧
      0 < d.signedDegree 5 ∧ 0 < d.signedDegree 6 := by
    rcases threeInduced_signed_degree_alternatives S hS t ht e d with ⟨hz, _⟩ | ⟨hz, _⟩ <;>
      (rw [hz]; decide)
  have h0 := degreeSign_of_pos d 0 hpos.1
  have h1 := degreeSign_of_neg d 4 hpos.2.1
  have h2 := degreeSign_of_pos d 5 hpos.2.2.1
  have h3 := degreeSign_of_pos d 6 hpos.2.2.2
  change d.sign 0 = 1 at h0
  change d.sign 1 = -1 at h1
  change d.sign 2 = 1 at h2
  change d.sign 3 = 1 at h3
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3]

include hS ht in
/-- Positive degrees of the actual characters and the corresponding group order. -/
public theorem threeInduced_degree_order_alternatives :
    (d.degree = ![10,11,10,10,55,44,45] ∧ Nat.card G = 7920) ∨
    (d.degree = ![26,27,26,26,39,12,13] ∧ Nat.card G = 5616) := by
  rcases threeInduced_signed_degree_alternatives S hS t ht e d with ⟨hz, hg⟩ | ⟨hz, hg⟩
  · left
    refine ⟨?_, hg⟩
    funext i
    rw [← degree_natAbs d i, hz]
    fin_cases i <;> norm_num
  · right
    refine ⟨?_, hg⟩
    funext i
    rw [← degree_natAbs d i, hz]
    fin_cases i <;> norm_num

include hS ht in
/-- Appendix equation (12) for χ₁ on D, with ε resolved to 1. -/
public theorem threeInduced_first_restriction_resolved
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    d.χ 0 a = threeCentralizerCharacter t e 0 a - threeCentralizerCharacter t e 3 a -
      threeCentralizerCharacter t e 6 a - threeCentralizerCharacter t e 7 a := by
  simpa [threeInduced_signs S hS t ht e d] using
    threeInduced_first_restriction t ht e d a ha

include hS ht in
/-- Appendix equation (12) for χ₆ on D, with ε₂ resolved to 1. -/
public theorem threeInduced_sixth_restriction_resolved
    (a : Subgroup.centralizer ({t} : Set G)) (ha : t ∈ Subgroup.zpowers (a : G)) :
    d.χ 5 a = -threeCentralizerCharacter t e 5 a := by
  simpa [threeInduced_signs S hS t ht e d] using
    threeInduced_sixth_restriction t ht e d a ha

include hS ht in
/-- The involution values of all seven genuine irreducibles, after resolving signs. -/
public theorem threeInduced_involution_vector (i : Fin 7) :
    d.χ i t = (![2,3,-2,-2,-1,4,-3] i : ℂ) := by
  have h := threeInduced_signed_involution_vector t ht e d i
  have hs := threeInduced_signs S hS t ht e d
  have h0 : (d.sign 0 : ℂ) = 1 := by
    exact_mod_cast (show d.sign 0 = 1 from congrFun hs 0)
  have h1 : (d.sign 1 : ℂ) = -1 := by
    exact_mod_cast (show d.sign 1 = -1 from congrFun hs 1)
  have h2 : (d.sign 2 : ℂ) = 1 := by
    exact_mod_cast (show d.sign 2 = 1 from congrFun hs 2)
  have h3 : (d.sign 3 : ℂ) = 1 := by
    exact_mod_cast (show d.sign 3 = 1 from congrFun hs 3)
  fin_cases i
  · change (d.sign 0 : ℂ) * d.χ 0 t = 2 at h
    change d.χ 0 t = 2
    simpa only [h0, one_mul] using h
  · change (d.sign 0 : ℂ) * d.χ 1 t = 3 at h
    change d.χ 1 t = 3
    simpa only [h0, one_mul] using h
  · change (d.sign 0 : ℂ) * d.χ 2 t = -2 at h
    change d.χ 2 t = -2
    simpa only [h0, one_mul] using h
  · change (d.sign 0 : ℂ) * d.χ 3 t = -2 at h
    change d.χ 3 t = -2
    simpa only [h0, one_mul] using h
  · change (d.sign 1 : ℂ) * d.χ 4 t = 1 at h
    rw [h1] at h
    change d.χ 4 t = -1
    linear_combination -h
  · change (d.sign 2 : ℂ) * d.χ 5 t = 4 at h
    change d.χ 5 t = 4
    simpa only [h2, one_mul] using h
  · change (d.sign 3 : ℂ) * d.χ 6 t = -3 at h
    change d.χ 6 t = -3
    simpa only [h3, one_mul] using h

/-- The complete character catalog, enhanced with the equations, positive
alternatives, resolved signs and Appendix restrictions for these same witnesses. -/
public structure ThreeGlobalDegreeData (G : Type*) [Group G] [Finite G]
    extends ThreeInducedCharacterData G where
  degree_congruence : 8 ∣ decomposition.signedDegree 0 - 2
  first_degree_equation :
    (Nat.card G : ℤ) * (decomposition.signedDegree 0 - 2)^2 =
      4608*decomposition.signedDegree 0*(decomposition.signedDegree 0+1)
  second_degree_equation :
    let x := decomposition.signedDegree 0
    let y := decomposition.signedDegree 5
    y^2*(2*x-1)*(x-8) + 2*y*(x+1)*(x^2-16*x+4) - 16*x*(x+1)^2 = 0
  signs : decomposition.sign = ![1,-1,1,1]
  degree_alternatives :
    (decomposition.degree = ![10,11,10,10,55,44,45] ∧ Nat.card G = 7920) ∨
    (decomposition.degree = ![26,27,26,26,39,12,13] ∧ Nat.card G = 5616)
  first_restriction : ∀ a : Subgroup.centralizer ({involution} : Set G),
    involution ∈ Subgroup.zpowers (a : G) →
    decomposition.χ 0 a = threeCentralizerCharacter involution centralizerEquiv 0 a -
      threeCentralizerCharacter involution centralizerEquiv 3 a -
      threeCentralizerCharacter involution centralizerEquiv 6 a -
      threeCentralizerCharacter involution centralizerEquiv 7 a
  sixth_restriction : ∀ a : Subgroup.centralizer ({involution} : Set G),
    involution ∈ Subgroup.zpowers (a : G) →
    decomposition.χ 5 a = -threeCentralizerCharacter involution centralizerEquiv 5 a

include hS in
/-- Final assembly under the original finite-simple, semidihedral Sylow-order-16,
and actual GL₂(3)-centralizer hypotheses. -/
public theorem exists_threeGlobalDegreeData
    (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nonempty (ThreeGlobalDegreeData G) := by
  obtain ⟨c⟩ := exists_threeInducedCharacterData S hS hcard hC
  obtain ⟨hc, ho, hq⟩ := threeInduced_global_degree_identities S hS
    c.involution c.order_involution c.centralizerEquiv c.decomposition
  exact ⟨{
    toThreeInducedCharacterData := c
    degree_congruence := hc
    first_degree_equation := ho
    second_degree_equation := hq
    signs := threeInduced_signs S hS c.involution c.order_involution
      c.centralizerEquiv c.decomposition
    degree_alternatives := threeInduced_degree_order_alternatives S hS c.involution
      c.order_involution c.centralizerEquiv c.decomposition
    first_restriction := threeInduced_first_restriction_resolved S hS c.involution
      c.order_involution c.centralizerEquiv c.decomposition
    sixth_restriction := threeInduced_sixth_restriction_resolved S hS c.involution
      c.order_involution c.centralizerEquiv c.decomposition }⟩

end
end ABG
