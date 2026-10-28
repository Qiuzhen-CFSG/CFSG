module

public import Stellmacher.Recognition.LyonsU3Four.AmbientSectionPreliminaries
public import Theory.Character.ModularBlock.SectionOrthogonality
public import Stellmacher.Recognition.LyonsU3Four.LocalFiveSectionGram
public import Stellmacher.Recognition.LyonsU3Four.BrauerColumnCoefficientTransfer

/-!
# Ambient coefficient pairings for the Lyons sections

Disjointness of the order-four and involution sections makes their block kernel
zero. Independence of the genuine local Brauer characters then annihilates each
of the five mixed coefficient pairings separately. Brauer transfer identifies
the induced genuine local columns with the supplied coefficient columns. Their
full Gram matrix then proves equation (3.2), retaining the actual odd core.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), pp. 373--374,
equation (3.2), and the induction argument on p. 381.
-/

public section
noncomputable section
open scoped BigOperators
namespace Stellmacher.Recognition.LyonsU3Four
open Subgroup ModularBlock PrincipalBlockConstruction
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
/-- The model's enumeration is exactly the ordered power basis used in (3.1). -/
theorem FiveSectionModel.basis_compatibility {S : Sylow 2 G} {z : G}
    (M : FiveSectionModel S z) (i : Fin 5) (v : centralizer ({z} : Set G)) :
    M.mu v ^ GeneralizedDecompositionData.basicExponent i =
      M.enumeration i (M.quotientEquiv (QuotientGroup.mk' (pPrimeCore 2 _) v)).right := by
  rw [M.enumeration_apply, M.mu_apply]
  rfl

/-- Each involution coefficient column is orthogonal to the order-four column. -/
theorem ambient_section_tz
    (S : Sylow 2 G) (b : PrincipalCongruenceBlockData G)
    (t : S) (ht : orderOf t = 4)
    (M : FiveSectionModel S ((t : G)^2)) (a : M.BrauerData b)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g))
      (t : G) ((t : G)^2) M.mu) (i : Fin 5) :
    GeneralizedDecompositionData.columnInner c.dT (c.iDz i) = 0 := by
  have htG : orderOf (t : G) = 4 := (Subgroup.orderOf_coe t).trans ht
  have ht4 : (t : G)^4 = 1 := by rw [← htG]; exact pow_orderOf_eq_one _
  have ht2 : ∃ n : ℕ, (t : G)^(2^n) = 1 := ⟨2, ht4⟩
  have hz2 : ∃ n : ℕ, ((t : G)^2)^(2^n) = 1 :=
    ⟨1, by simpa [← pow_mul] using ht4⟩
  have hne : ¬ IsConj (t : G) ((t : G)^2) := by
    intro hconj
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have ho := (MulAut.conj g).orderOf_eq (t : G)
    rw [MulAut.conj_apply, hg, orderOf_pow, htG] at ho
    norm_num at ho
  have hz (v : centralizer ({(t : G)^2} : Set G)) (hv : Odd (orderOf v)) :
      ∑ j : {j // j ∈ b.block}, (c.dT j : ℂ) *
        b.chi j.1 (ConjClasses.mk ((t : G)^2 * (v : G))) = 0 := by
    have hk := SectionOrthogonality.principalBlock_column_eq_zero_of_not_mem_twoSection
      b (t : G) ht2 ((t : G)^2 * (v : G)) (by
        intro hs
        apply hne
        apply Theory.Character.isConj_of_mem_twoSection ht2 hz2 hs
        exact ⟨v, by simpa using hv,
          (mem_centralizer_singleton_iff.mp v.property).symm, IsConj.refl _⟩)
    rw [Finset.sum_subtype b.block (fun _ => Iff.rfl)] at hk
    simp_rw [GeneralizedDecompositionData.Equation3_1.at_t c he] at hk
    have hh := congrArg star hk
    simpa only [star_sum, star_mul, star_intCast, star_star, star_zero, mul_comm] using hh
  have hc : (fun k => (GeneralizedDecompositionData.columnInner c.dT (c.iDz k) : ℂ)) =
      (fun _ => (0 : ℂ)) := by
    apply TwistedBrauerExpansion.coefficients_unique _ a.decomposition
    intro v hv
    simp only [zero_mul, Finset.sum_const_zero]
    rw [← hz v hv]
    simp_rw [he.2 _ v hv, ← a.value _ v hv]
    simp only [GeneralizedDecompositionData.columnInner, Int.cast_sum, Int.cast_mul,
      Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  exact_mod_cast congrFun hc i
/-- Transfer the full local Gram matrix after the actual induction identity has
been established. This assembly lemma does not assert that induction identity. -/
theorem ambient_section_equation3_2_of_induction
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (M : FiveSectionModel S ((t : G)^2)) (a : M.BrauerData b)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g))
      (t : G) ((t : G)^2) M.mu)
    (T : LocalFiveCharacterTable S M.α) (w : QuarticCentralIndex S)
    (hw : (w.1.1 : G) = (t : G)^2)
    (hind : ∀ i : Fin 5,
      inducedClassFunction (centralizer ({(t : G)^2} : Set G))
        (T.inflatedSectionClassFunction w (pPrimeCore 2 _) M.quotientEquiv (M.enumeration i)) =
        ∑ j : {j // j ∈ b.block}, (c.iDz i j : ℂ) • ofConjClassFunction (b.chi j.1)) :
    c.Equation3_2 := by
  refine ⟨ambient_section_tt S d b t ht M.mu c he,
    ambient_section_tz S b t ht M a c he, ?_⟩
  intro i k
  have hz : orderOf ((t : G)^2) = 2 := by
    rw [orderOf_pow, Subgroup.orderOf_coe, ht]; decide
  have hp := T.inducedSectionClassFunction_gram h M.β M.order_β M.action
    M.central hz M.quotientEquiv M.preservesSylow w hw (M.enumeration i) (M.enumeration k)
  rw [hind i, hind k] at hp
  have ho (j l : {j // j ∈ b.block}) :
      scalarProduct G (ofConjClassFunction (b.chi j.1))
        (ofConjClassFunction (b.chi l.1)) = if j = l then 1 else 0 := by
    change classFunctionInner (b.chi j.1) (b.chi l.1) = _
    rw [completeFamily_orthonormal b.complete]
    simp only [Subtype.val_inj]
  rw [scalarProduct_integer_columns _ ho] at hp
  simp only [M.enumeration.injective.eq_iff] at hp
  change (GeneralizedDecompositionData.columnInner (c.iDz i) (c.iDz k) : ℂ) = _ at hp
  exact_mod_cast hp

/-- Genuine integral expansions (3.1) satisfy all of the Gram identities (3.2).
The local table and its induction identity are constructed from the model;
neither an induction hypothesis nor a trivial odd core is required. -/
theorem ambient_section_equation3_2
    (S : Sylow 2 G) (h : SylowStructure S) (d : LocalCentralizerData S)
    (b : PrincipalCongruenceBlockData G) (t : S) (ht : orderOf t = 4)
    (M : FiveSectionModel S ((t : G)^2)) (a : M.BrauerData b)
    (c : GeneralizedDecompositionData {j // j ∈ b.block})
    (he : c.Equation3_1 (fun j g => b.chi j.1 (ConjClasses.mk g))
      (t : G) ((t : G)^2) M.mu) :
    c.Equation3_2 := by
  obtain ⟨T⟩ := exists_localFiveCharacterTable S M.α h M.β M.order_β M.action
  have hz := orderFour_square_mem_centerImage S h t ht
  let w : QuarticCentralIndex S :=
    ⟨⟨t ^ 2, square_mem_center S h t⟩, by
      intro heq
      exact hz.2 (congrArg (fun x : Subgroup.center S => (x.1 : G)) heq)⟩
  have hw : (w.1.1 : G) = (t : G)^2 := rfl
  have hz2 : orderOf ((t : G)^2) = 2 := by
    rw [orderOf_pow, Subgroup.orderOf_coe, ht]; decide
  apply ambient_section_equation3_2_of_induction S h d b t ht M a c he T w hw
  intro i
  have hind := T.induced_inflatedSectionClassFunction_eq_iDz h M.central hz2
    M.quotientEquiv M.preservesSylow w hw b c (t : G) M.mu he M.enumeration
    (fun k v _ => M.basis_compatibility k v) i
  rw [Subsingleton.elim (Fintype.ofFinite {j // j ∈ b.block})
    (Finset.Subtype.fintype b.block)] at hind
  exact hind

end Stellmacher.Recognition.LyonsU3Four
