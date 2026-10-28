module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Three
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.Catalogue
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph

/-!
# The nonnormal-component outer inspection on the complete source catalogue

All full Theorem C models have abelian outer group or two-group outer group,
except for possible cubic diagonal action in degree three. The preceding
source rank argument excludes that diagonal action for an actual nonnormal
component. Every case below retains its literal matrix, form, fixed-group or
sporadic model and the perfect central-cover embedding on outer groups.

The disjunction is exactly what Proposition 1.3.4 needs: an odd acting group
has abelian image in the first case and trivial image in the second.
Source: Aschbacher–Smith A.3.8, pp.45–46, and 1.3.4, p.510.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
open Chapter1.Section02 Chapter1.XiEmbedding.OuterModels

private theorem commutative_cover {B S : Type*} [Group B] [Group S]
    [Group.IsPerfect B] (e : B ⧸ center B ≃* S) [IsMulCommutative (MulAut.Outer S)] :
    IsMulCommutative (MulAut.Outer B) ∨ IsPGroup 2 (MulAut.Outer B) :=
  Or.inl (MulAut.outer_isMulCommutative_of_centralQuotient e)

private theorem two_cover {B S : Type*} [Group B] [Group S]
    [Group.IsPerfect B] (e : B ⧸ center B ≃* S) (h : IsPGroup 2 (MulAut.Outer S)) :
    IsMulCommutative (MulAut.Outer B) ∨ IsPGroup 2 (MulAut.Outer B) :=
  Or.inr (h.of_injective (MulAut.centralQuotientOuter e)
    (MulAut.centralQuotientOuter_injective e))

private theorem alternating_two (n : ℕ) (hn : 5 ≤ n) :
    IsPGroup 2 (MulAut.Outer (alternatingGroup (Fin n))) := by
  by_cases he : n = 6
  · subst n
    exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
  let A := alternatingGroup (Fin n)
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card (Equiv.Perm (Fin n) ⧸ A) = 2 ^ 1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hcard).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨σ, rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn he).surjective a
  exact ⟨QuotientGroup.mk' A σ, rfl⟩

/-- Full source model inspection on the actual nonnormal component.
No four-model reduction or extra automorphism hypothesis is assumed. -/
theorem nonnormal_outer_of_model {G : Type*} [Group G] [Finite G]
    (hG : primeRank 3 G ≤ 2) (hcore : pCore 2 G = ⊥)
    (B : Subgroup G) (hB : IsComponent G B) (hnormal : ¬ B.Normal)
    (hmodel : LocalModels.TheoremCModel (B ⧸ center B)) :
    IsMulCommutative (MulAut.Outer B) ∨ IsPGroup 2 (MulAut.Outer B) := by
  let : IsQuasisimple B := hB.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : IsQuasisimple (B ⧸ center B) :=
    IsQuasisimple.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  cases hmodel with
  | alternating n hn he => exact two_cover he.some (alternating_two n hn.1)
  | linear_odd p n hp ho hn _ he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    exact two_cover e (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      hp ho (by rcases hn with rfl | rfl <;> omega) hF)
  | three_odd p hp ho unitary he =>
    cases unitary with
    | false => exact Or.inl (linear_odd_outer hG B hB hnormal p hp ho he)
    | true => exact Or.inl (unitary_odd_outer hG hcore B hB hnormal p hp ho he)
  | rank_one he =>
    cases he with
    | linear n hn he =>
      let := psl2_binary_model_outer_isMulCommutative n hn he
      exact commutative_cover (MulEquiv.refl _)
    | unitary n hn he => exact Or.inl (unitary_even_outer hG hcore B hB hnormal n hn he)
    | suzuki m hm he =>
      let := suzuki_outer_isCyclic m hm
      exact commutative_cover he.some
  | rank_two he =>
    cases he with
    | linear n hn he => exact Or.inl (linear_even_outer hG hcore B hB hnormal n hn he)
    | symplectic n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      let := Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card
        hF (by omega : 1 < n)
        Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
      exact commutative_cover (e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)
    | g2 n hn he =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      have hlarge : 2 < Nat.card F := by
        rw [hF]
        have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
        norm_num at hh
        omega
      let := g2_outer_isCyclic_of_coverage
        (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective (F := F) hlarge)
      exact commutative_cover e
    | triality n hn he =>
      obtain ⟨P, hq, ⟨e⟩⟩ := he
      let : IsSimpleGroup (Triality.Standard.Carrier P) := e.symm.isSimpleGroup
      let : Group.IsPerfect (Triality.Standard.Carrier P) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := Triality.Standard.OuterOdd.outer_isCyclic P n hn hq
      exact commutative_cover e
    | ree m hm he =>
      obtain ⟨d, ⟨e⟩⟩ := he
      let : IsSimpleGroup d.fixedGroup := e.symm.isSimpleGroup
      let : Group.IsPerfect d.fixedGroup :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      let := ReeF4.LocalBlockInput.outer_isCyclic hm d
      exact commutative_cover e
    | symplectic_derived he =>
      let := AlternatingSix.ShadowLocal.outer_isMulCommutative
      exact commutative_cover (he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived he =>
      let := g2_derived_outer_isCyclic_of_coverage
        Atlas.G2.LieAutomorphismExtensions.binaryConjugation_surjective
      exact commutative_cover he.some
    | tits he => exact two_cover he.some Tits.OuterOddSubgroups.parrott_outer_isPGroup
  | binary_linear n hn he =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := he
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
    let := BinaryLinear.OuterCyclic.psl_outer_isCyclic hn
    exact commutative_cover (e.trans (Atlas.fieldEquivPSL n eF))
  | sporadic name hne he =>
    cases name with
    | m11 => exact two_cover he.some Sporadic.Mathieu.m11_outer_isPGroup_two
    | m12 => exact two_cover he.some (m12_outer_isPGroup_two_of_sylow_aut
        Sporadic.Mathieu.M12SmallPair.SylowAutomorphismGroup.isPGroup_two)
    | m22 => exact two_cover he.some (m22_outer_isPGroup_two_of_coverage
        Sporadic.Mathieu.m22DesignAutToAut_surjective)
    | m23 => exact two_cover he.some Sporadic.Mathieu.m23_outer_isTwoGroup
    | m24 => exact two_cover he.some Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
    | j2 => exact two_cover he.some JankoTwo.outer_isPGroup_two
    | hs => exact two_cover he.some (Sporadic.LeechRelated.HS.outer_isPGroup_two_of_pointStabilizer_map
        Sporadic.LeechRelated.HS.pointStabilizer_map Sporadic.LeechRelated.HS.normalizer_relIndex_dvd_two_pow)
    | ru =>
      let : IsSimpleGroup Rudvalis.Model := he.some.symm.isSimpleGroup
      let := rudvalis_outer_subsingleton
      let : IsMulCommutative (MulAut.Outer Rudvalis.Model) :=
        ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
      exact commutative_cover (show _ ≃* Rudvalis.Model from he.some)
    | j3 => exact (hne rfl).elim
    | he => exact two_cover he.some (Subgroup.isPGroup_outer_of_normalizer
        Held.permutationGroup 2 Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient)
    | j4 => exact two_cover he.some Janko4.AdequateLocal.outer_isPGroup_two
  | janko_one he =>
    let := janko_one_outer_isMulCommutative he.some
    exact commutative_cover (MulEquiv.refl _)

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource
