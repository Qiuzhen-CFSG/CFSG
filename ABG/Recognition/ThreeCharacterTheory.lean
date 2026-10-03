module
public import ABG.Recognition.ThreeGlobalDegreeIdentities

/-!
# Wong's characteristic-three character theorem

A finite simple group with a semidihedral Sylow 2-subgroup of order 16 and
GL₂(3) involution centralizers has order 7920 or 5616. The theorem retains the
seven distinct nontrivial irreducible characters, their actual degrees, the
five induction identities, and vanishing and degree divisibility for every
remaining nontrivial irreducible. All statements use one shared catalog.

The representation and induction constructions, involution-pair identities,
and integer degree calculation are assembled from the preceding modules.
The five induction identities and the two Appendix restrictions determine
all seven restrictions on D = {a ∈ C_G(t) | t ∈ ⟨a⟩}. These are restrictions
to D, not identities on the whole centralizer.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2”, §4, pp.97–104, and Appendix, pp.106–107 (1964),
DOI 10.1017/S1446788700022771.
-/

namespace ABG
open BenderGlauberman
noncomputable section

/-- The seven restrictions on D, in terms of the eight local characters.
Both the global and local indices start at zero. -/
@[expose] public def threeCharacterRootRestriction (φ : Fin 8 → ℂ) : Fin 7 → ℂ :=
  ![φ 0 - φ 3 - φ 6 - φ 7,
    φ 0 - φ 2 - φ 3 + φ 4 - φ 6 - φ 7,
    φ 0 - φ 2 - φ 3 - φ 7,
    φ 0 - φ 2 - φ 3 - φ 6,
    φ 0 - φ 1 - φ 2 - φ 3 - φ 6 - φ 7,
    -φ 5, -φ 3]

/-- The resolved induction identities determine every distinguished character
on the roots of the central involution. -/
public theorem ThreeGlobalDegreeData.root_restrictions
    {G : Type*} [Group G] [Finite G] (c : ThreeGlobalDegreeData G)
    (a : Subgroup.centralizer ({c.involution} : Set G))
    (ha : c.involution ∈ Subgroup.zpowers (a : G)) (i : Fin 7) :
    c.decomposition.χ i a = threeCharacterRootRestriction
      (fun j => threeCentralizerCharacter c.involution c.centralizerEquiv j a) i := by
  have h0 := congrFun c.decomposition.first (a : G)
  have h1 := congrFun c.decomposition.second (a : G)
  have h2 := congrFun c.decomposition.third (a : G)
  have h3 := congrFun c.decomposition.fourth (a : G)
  have h4 := congrFun c.decomposition.fifth (a : G)
  simp only [c.signs, Matrix.cons_val, Int.cast_one, Int.cast_neg,
    Pi.add_apply, Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
    one_mul, neg_one_mul,
    threeInducedGenerator_apply_root c.involution c.order_involution c.centralizerEquiv _ a ha]
    at h0 h1 h2 h3 h4
  have hg (k : Fin 5) : threeCentralizerGenerator c.involution c.centralizerEquiv k a =
      ![threeCentralizerCharacter c.involution c.centralizerEquiv 0 a +
          threeCentralizerCharacter c.involution c.centralizerEquiv 2 a -
          threeCentralizerCharacter c.involution c.centralizerEquiv 4 a,
        threeCentralizerCharacter c.involution c.centralizerEquiv 2 a -
          threeCentralizerCharacter c.involution c.centralizerEquiv 6 a,
        threeCentralizerCharacter c.involution c.centralizerEquiv 6 a -
          threeCentralizerCharacter c.involution c.centralizerEquiv 7 a,
        threeCentralizerCharacter c.involution c.centralizerEquiv 1 a +
          threeCentralizerCharacter c.involution c.centralizerEquiv 4 a -
          threeCentralizerCharacter c.involution c.centralizerEquiv 5 a,
        threeCentralizerCharacter c.involution c.centralizerEquiv 1 a +
          threeCentralizerCharacter c.involution c.centralizerEquiv 2 a -
          threeCentralizerCharacter c.involution c.centralizerEquiv 3 a] k := by
    fin_cases k <;> rfl
  simp only [hg, Matrix.cons_val] at h0 h1 h2 h3 h4
  have hf := c.first_restriction a ha
  have hs := c.sixth_restriction a ha
  have ht : threeCentralizerCharacter c.involution c.centralizerEquiv 0 a = 1 := rfl
  fin_cases i <;> simp only [Fin.reduceFinMk, threeCharacterRootRestriction, Matrix.cons_val]
  · exact hf
  · linear_combination hf + h0 - ht
  · linear_combination hf + h1
  · linear_combination hf + h1 + h2
  · linear_combination hf + h0 + hs + h3 - ht
  · exact hs
  · linear_combination -h4 + h0 + hs + h3 - ht

/-- Wong's characteristic-three character theorem, with all witnesses,
degree alternatives, induction identities and Appendix restrictions retained. -/
public theorem exists_threeCharacterTheory
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nonempty (ThreeGlobalDegreeData G) :=
  exists_threeGlobalDegreeData S hS hcard hC

/-- The two possible orders under the original local group hypotheses. -/
public theorem threeCharacterTheory_order_alternatives
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nat.card G = 7920 ∨ Nat.card G = 5616 := by
  obtain ⟨c⟩ := exists_threeCharacterTheory S hS hcard hC
  exact c.degree_alternatives.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2)

end
end ABG
