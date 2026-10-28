module

public import Theory.Representation.FirstCohomologyLinearTransport
public import Theory.Representation.SpecialLinearNatural
public import Theory.Representation.SL2NaturalFirstCohomology
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.Representation.SL5TenDimensionalFirstCohomology
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive
public import Theory.Representation.BinaryAlternatingNaturalCohomology.Projective
public import Theory.Representation.ProjectivityTransport

/-!
# I.1.6: linear-group first cohomology

This module proves the linear-group clauses (2), (3), (4), (6), and (7) of
Aschbacher--Smith's Lemma I.1.6. All cohomology dimensions are over F₂, using
the explicit quotient of crossed homomorphisms by principal ones. The natural
SL₂ and SL₃ calculations retain the defining-field degree and the SL₃(2)
exception. The L₄(2) and L₅(2) statements use the canonical projective quotient,
and the ten-dimensional assertion ranges over every irreducible module.

The imported calculations normalize cocycles on elementary matrices, descend
the twisted tensor calculation to Hermitian matrices, and classify the
ten-dimensional irreducibles by exterior powers. Explicit equivariant group
and vector-space isomorphisms transport these results to arbitrary realizations
of the source modules. The earlier general scalar-restriction formula is retained.

The orthogonal module is the four-dimensional Hermitian minus-type model over
F_(2ⁿ), of binary dimension 4n. At n = 1 its five singular vectors give an actual
equivariant identification with the natural deleted-permutation A₅ module.
Transport of that module's proved group-algebra projectivity establishes the
additional projectivity clause. The natural two-dimensional F₄ module is a
different representation, with binary first-cohomology dimension two.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(2), (3), (4), (6), (7), printed p.408
(PDF p.419). The source cites W. Jones and B. Parshall, “On the 1-cohomology of
finite groups of Lie type”, Proceedings of the Conference on Finite Groups
(1976), pp.313–328; the A₅ calculation is Exercise 6.3 of [Asc86a].
-/

namespace CFSG.Quasithin.ChapterI

open Representation Representation.OneCohomology

/-- An honest natural-module identification reduces the cohomology dimension
over `k` to the canonical matrix calculation over `K`. -/
public theorem finrank_firstCohomology_of_natural
    {k K G V : Type*} [Field k] [Field K] [Algebra k K]
    [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (d : ℕ)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin d) K)
    (eV : V ≃ₗ[k] (Fin d → K))
    (he : ∀ g v, eV (ρ g v) = specialLinearNatural d (eG g) (eV v)) :
    Module.finrank k (H1 ρ) =
      Module.finrank k K * Module.finrank K (H1 (specialLinearNatural (k := K) d)) := by
  let σ := restrictScalars (k := k) (specialLinearNatural (k := K) d)
  have e : H1 ρ ≃ₗ[k] H1 σ := H1Congr ρ σ eG eV he
  rw [e.finrank_eq]
  exact finrank_restrictScalars _

/-- I.1.6(2): the natural L₂(2ⁿ) module has binary first-cohomology dimension n
for n > 1. The action is the actual characteristic-two projective matrix action. -/
public theorem psl2Natural_firstCohomology_finrank
    {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    (n : ℕ) (hn : 1 < n) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (SL2NaturalH1.projectiveNatural (K := K)))) = n :=
  SL2NaturalH1.finrank_projective_restrict_eq n hn hK

/-- I.1.6(2) for an arbitrary realization of the natural module, with its
group isomorphism and binary equivariant coordinates explicit. -/
public theorem psl2Natural_firstCohomology_finrank_of_equiv
    {K G V : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (n : ℕ) (hn : 1 < n) (hK : Nat.card K = 2 ^ n)
    (eG : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (eV : V ≃ₗ[ZMod 2] (Fin 2 → K))
    (he : ∀ g v, eV (ρ g v) = SL2NaturalH1.projectiveNatural (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) = n := by
  rw [(H1Congr ρ (restrictScalars (k := ZMod 2) (SL2NaturalH1.projectiveNatural (K := K)))
    eG eV he).finrank_eq]
  exact psl2Natural_firstCohomology_finrank n hn hK

/-- I.1.6(4): the natural SL₃(2ⁿ) module has binary first-cohomology
dimension one at n = 1 and zero at n > 1. -/
public theorem sl3Natural_firstCohomology_finrank
    {K : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    (n : ℕ) (hK : Nat.card K = 2 ^ n) :
    Module.finrank (ZMod 2)
      (H1 (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))) =
      if n = 1 then 1 else 0 :=
  SLHigherNatural.finrank_restrict_sl3_of_card_pow n hK

/-- The SL₃ calculation for any equivariantly identified natural module.
The defining-field action is restricted to F₂ before computing H¹. -/
public theorem sl3Natural_firstCohomology_finrank_of_equiv
    {K G V : Type*} [Field K] [Finite K] [CharP K 2] [Algebra (ZMod 2) K]
    [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (n : ℕ) (hK : Nat.card K = 2 ^ n)
    (eG : G ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    (eV : V ≃ₗ[ZMod 2] (Fin 3 → K))
    (he : ∀ g v, eV (ρ g v) = specialLinearNatural 3 (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) = if n = 1 then 1 else 0 := by
  rw [(H1Congr ρ (restrictScalars (k := ZMod 2) (specialLinearNatural (k := K) 3))
    eG eV he).finrank_eq]
  exact sl3Natural_firstCohomology_finrank n hK

/-- I.1.6(6): first cohomology vanishes for the natural L₄(2) and L₅(2)
modules, using the canonical SL-to-PSL quotient identification. -/
public theorem pslFourFiveNatural_firstCohomology_finrank
    (d : ℕ) (hd : d = 4 ∨ d = 5) :
    Module.finrank (ZMod 2) (H1 (SLHigherNatural.binaryProjectiveNatural d)) = 0 :=
  SLHigherNatural.finrank_H1_binaryProjective_of_four_le (by rcases hd with rfl | rfl <;> decide)

/-- The natural L₄(2) and L₅(2) vanishing assertion in arbitrary
equivariant group and module coordinates. -/
public theorem pslFourFiveNatural_firstCohomology_finrank_of_equiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (d : ℕ) (hd : d = 4 ∨ d = 5)
    (eG : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2))
    (eV : V ≃ₗ[ZMod 2] (Fin d → ZMod 2))
    (he : ∀ g v, eV (ρ g v) = SLHigherNatural.binaryProjectiveNatural d (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  rw [(H1Congr ρ (SLHigherNatural.binaryProjectiveNatural d) eG eV he).finrank_eq]
  exact pslFourFiveNatural_firstCohomology_finrank d hd

/-- I.1.6(7): every ten-dimensional irreducible binary L₅(2) module has
zero first cohomology. The exhaustive model classification and the exterior
cohomology calculations are discharged by the imported theorem. -/
public theorem pslFiveTenDimensional_firstCohomology_finrank
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) V)
    [IsIrreducible ρ] (hdim : Module.finrank (ZMod 2) V = 10) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 :=
  SL5TenDimensional.projective_finrank_h1_eq_zero_of_finrank_ten ρ hdim

/-- I.1.6(7) for a group identified with L₅(2); no choice of an
irreducible isomorphism class or additional cohomology premise is required. -/
public theorem pslFiveTenDimensional_firstCohomology_finrank_of_equiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (eG : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2))
    (hdim : Module.finrank (ZMod 2) V = 10) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  let := SL5TenDimensional.h1_subsingleton_of_group_equiv ρ
    (eG.trans SL5TenDimensional.projectiveEquiv.symm) hdim
  exact Module.finrank_zero_of_subsingleton

open OrthogonalFourMinus.FiniteModel

/-- I.1.6(3): the four-dimensional minus-type orthogonal module over
F_(2ⁿ) has zero binary first cohomology for every positive n. The actual
Hermitian module has binary dimension 4n, as proved by `finrank_binary_space`. -/
public theorem orthogonalFourMinus_firstCohomology_finrank (n : ℕ) [NeZero n] :
    Module.finrank (ZMod 2) (H1 (binaryPSL2Action n)) = 0 :=
  finrank_H1_binaryPSL2Action n

/-- The orthogonal vanishing assertion for any module explicitly identified
with the Hermitian minus-type model and its actual PSL₂ action. -/
public theorem orthogonalFourMinus_firstCohomology_finrank_of_equiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (n : ℕ) [NeZero n]
    (eG : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n))
    (eV : V ≃ₗ[ZMod 2] Space n)
    (he : ∀ g v, eV (ρ g v) = binaryPSL2Action n (eG g) (eV v)) :
    Module.finrank (ZMod 2) (H1 ρ) = 0 := by
  rw [(H1Congr ρ (binaryPSL2Action n) eG eV he).finrank_eq]
  exact orthogonalFourMinus_firstCohomology_finrank n


/-- The identification clause of I.1.6(3): the orthogonal L₂(4) module
is equivariantly isomorphic to the four-dimensional natural A₅ module.
The witnesses come from the action on the five singular Hermitian vectors. -/
public theorem orthogonalFourMinusSmall_equiv_alternatingNatural :
    ∃ eG : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1) ≃*
        alternatingGroup (Fin 5),
      ∃ eV : Space 1 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5),
        ∀ g v, eV (binaryPSL2Action 1 g v) =
          BinaryPermutation.alternatingNaturalRepresentation (Fin 5) (eG g) (eV v) :=
  ⟨OrthogonalFourMinus.AlternatingFive.psl2GroupEquiv,
    OrthogonalFourMinus.AlternatingFive.moduleEquiv,
    OrthogonalFourMinus.AlternatingFive.binaryPSL2Action_intertwines⟩

/-- The projectivity clause of I.1.6(3), over the actual binary group
algebra of L₂(4). It follows by transporting the proved A₅ projectivity
along the explicit group and module equivalences. -/
public theorem orthogonalFourMinusSmall_projective :
    Module.Projective
      (MonoidAlgebra (ZMod 2) (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1)))
      (binaryPSL2Action 1).asModule := by
  let := BinaryPermutation.alternatingFive_natural_projective
  exact Representation.projective_of_group_module_equiv (binaryPSL2Action 1)
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 5))
    OrthogonalFourMinus.AlternatingFive.psl2GroupEquiv
    OrthogonalFourMinus.AlternatingFive.moduleEquiv
    OrthogonalFourMinus.AlternatingFive.binaryPSL2Action_intertwines

/-- Projectivity of every equivariant realization of the orthogonal
L₂(4) module, with the group-algebra action transported as well. -/
public theorem orthogonalFourMinusSmall_projective_of_equiv
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (eG : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1))
    (eV : V ≃ₗ[ZMod 2] Space 1)
    (he : ∀ g v, eV (ρ g v) = binaryPSL2Action 1 (eG g) (eV v)) :
    Module.Projective (MonoidAlgebra (ZMod 2) G) ρ.asModule := by
  let := orthogonalFourMinusSmall_projective
  exact Representation.projective_of_group_module_equiv ρ (binaryPSL2Action 1) eG eV he

end CFSG.Quasithin.ChapterI
