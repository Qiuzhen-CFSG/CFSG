module
public import ABG.Recognition.ThreeCentralizerCharacters
public import ABG.Recognition.ThreeCharacterDecomposition
public import ABG.ChapterII.Section2.SimpleQD
public import Theory.Character.InvolutionRootVanishing
public import Theory.Character.VanishingDegree

/-!
# Wong's seven induced characters and remaining-character vanishing

The integral decomposition theorem applied to the five actual induced
functions gives Wong's seven distinct nontrivial irreducibles and four signs.
The supported local lattice detects vanishing on roots of the central
involution. Frobenius reciprocity applies this to any irreducible absent from
all five induced functions. The semidihedral simple-group fusion theorem
makes every even-order element conjugate to one of those roots. Finally,
restriction to the supplied Sylow subgroup gives degree divisibility by 16.
All conclusions refer to the same catalog in `ThreeCharacterDecomposition`.

Source: Wong (1964), equation (3), p.98 and Appendix equation (11), p.106.
-/

namespace ABG
open BenderGlauberman
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- Wong's five actual induced functions admit the seven-character form of
equation (3), for any supplied involution and centralizer equivalence. -/
public theorem exists_threeInducedCharacterDecomposition
    {G : Type*} [Group G] [Finite G]
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nonempty (ThreeCharacterDecomposition (threeInducedGenerator t e)) :=
  exists_threeCharacterDecomposition (threeInducedGenerator t e)
    (threeInducedGenerator_generalized t e)
    (threeInducedGenerator_one t ht e)
    (threeInducedGenerator_trivial_coefficient t e)
    (threeInducedGenerator_gram t ht e)

public theorem threeInduced_orthogonal_vanishes_even
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    {θ : ClassFunction G} (hθ : IsClassFunction θ)
    (ho : ∀ k : Fin 5, scalarProduct G θ (threeInducedGenerator t e k) = 0)
    (x : G) (hx : 2 ∣ orderOf x) : θ x = 0 := by
  have hQD := isQDGroup_of_simple ⟨S, hS⟩
  have hclass : HasElementConjugacyClassCount G 2 1 := by
    rcases hQD with ⟨_, _, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ <;> exact h.2.1
  have hfuse (u : G) (hu : orderOf u = 2) : IsConj u t := by
    obtain ⟨r, _, _, hcov⟩ := hclass
    obtain ⟨i, hi⟩ := hcov u hu
    obtain ⟨j, hj⟩ := hcov t ht
    exact hi.trans ((Subsingleton.elim i j) ▸ hj.symm)
  exact classFunction_vanishes_even_of_involution_roots t hfuse hθ
    (threeInduced_orthogonal_vanishes_on_roots t ht e hθ ho) x hx

/-- Every other nontrivial irreducible vanishes on all even-order elements. -/
public theorem threeInduced_remaining_character_vanishes
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S)
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e))
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ)
    (h1 : θ ≠ 1) (hχ : ∀ i, θ ≠ d.χ i)
    (x : G) (hx : 2 ∣ orderOf x) : θ x = 0 :=
  threeInduced_orthogonal_vanishes_even S hS t ht e
    (irreducibleCharacter_isClassFunction hθ) (d.orthogonal_of_not_mem hθ h1 hχ) x hx

/-- Divisibility applies to the same remaining character, with its actual degree. -/
public theorem threeInduced_remaining_character_degree
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e))
    {θ : ClassFunction G} (hθ : IsIrreducibleCharacter θ)
    (h1 : θ ≠ 1) (hχ : ∀ i, θ ≠ d.χ i) :
    ∃ n : ℕ, θ 1 = (n : ℂ) ∧ 16 ∣ n := by
  have h := character_degree_dvd_of_pSingular_vanishing (S : Subgroup G) S.isPGroup'
    (isCharacter_of_isIrreducibleCharacter hθ)
    (threeInduced_remaining_character_vanishes S hS t ht e d hθ h1 hχ)
  simpa only [hcard] using h

/-- A single catalog for Wong's induction identities and all the conclusions
about the remaining irreducibles. The local equivalence and the seven global
characters are retained, so subsequent degree calculations use these witnesses. -/
public structure ThreeInducedCharacterData (G : Type*) [Group G] [Finite G] where
  involution : G
  order_involution : orderOf involution = 2
  centralizerEquiv : Subgroup.centralizer ({involution} : Set G) ≃* GL2 3 1
  decomposition : ThreeCharacterDecomposition (threeInducedGenerator involution centralizerEquiv)
  remaining_vanishes : ∀ (θ : ClassFunction G), IsIrreducibleCharacter θ → θ ≠ 1 →
    (∀ i, θ ≠ decomposition.χ i) → ∀ x : G, 2 ∣ orderOf x → θ x = 0
  remaining_degree : ∀ (θ : ClassFunction G), IsIrreducibleCharacter θ → θ ≠ 1 →
    (∀ i, θ ≠ decomposition.χ i) → ∃ n : ℕ, θ 1 = (n : ℂ) ∧ 16 ∣ n

/-- Assemble the vanishing and divisibility statements without making a second
choice of irreducible characters. -/
public def threeInducedCharacterData_of_decomposition
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (t : G) (ht : orderOf t = 2)
    (e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeInducedGenerator t e)) :
    ThreeInducedCharacterData G where
  involution := t
  order_involution := ht
  centralizerEquiv := e
  decomposition := d
  remaining_vanishes θ hθ h1 hχ :=
    threeInduced_remaining_character_vanishes S hS t ht e d (θ := θ) hθ h1 hχ
  remaining_degree θ hθ h1 hχ :=
    threeInduced_remaining_character_degree S hS hcard t ht e d (θ := θ) hθ h1 hχ

/-- Cauchy's theorem selects the involution from the supplied Sylow subgroup,
and the supplied decompositions assemble the complete catalog. -/
public theorem exists_threeInducedCharacterData_of_decompositions
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hD : ∀ (t : G), orderOf t = 2 →
      ∀ e : Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1,
        Nonempty (ThreeCharacterDecomposition (threeInducedGenerator t e))) :
    Nonempty (ThreeInducedCharacterData G) := by
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (by rw [hcard]; norm_num)
  have ht : orderOf (s : G) = 2 := (Subgroup.orderOf_coe s).trans hs
  obtain ⟨d⟩ := hD s ht (hC s ht)
  exact ⟨threeInducedCharacterData_of_decomposition S hS hcard s ht (hC s ht) d⟩

/-- Wong's seven distinct nontrivial genuine irreducible characters and four
signs satisfy all five induction identities. Every other nontrivial irreducible
vanishes on even-order elements and has degree divisible by 16. The identities
and remaining-character statements use the same seven witnesses. -/
public theorem exists_threeInducedCharacterData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    Nonempty (ThreeInducedCharacterData G) :=
  exists_threeInducedCharacterData_of_decompositions S hS hcard hC
    exists_threeInducedCharacterDecomposition

end
end ABG
