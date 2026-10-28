module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Small Sylow models of the original C.2.7 star component

The genuine B.5.1 moved-section classifier supplies marked group models for
K* inside the offender-generated actor. Divisibility by the concrete unipotent
orders bounds the binary field degree by seven for SL₂ and by two for SL₃.
It eliminates larger symplectic and G₂ fields and the SL₅(2) endpoint. The
remaining small derived groups are retained with their actual equivalences;
the triple-six row retains both its cubic center and central quotient.

The source application carries every mark through the literal subgroup-of
identification back to `starImage K R K`. Its only additional premise is the
Sylow order bound supplied independently by the Chapter 14 Goldschmidt
consumer. It assumes no B.5 classification conclusion or model tag.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.2.7(3),
pp.145–147, and B.5.1/B.4.2, pp.99–103 and p.86, with the Sylow bound used
in the original 14.6.10(5) and 14.6.25 comparison on pp.1029–1030.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ProjectiveLine
namespace SmallModels
universe u v w
variable {D : Type u} [Group D] [Finite D]
variable {A : Type v} [Group A]

/-- A defining two-power divisor remains bounded through an actual embedding. -/
private theorem two_power_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (f : A →* D) (hf : Function.Injective f) {k : ℕ}
    (hd : 2 ^ k ∣ Nat.card A) : k ≤ 7 := by
  let S : Sylow 2 D := Classical.choice inferInstance
  have h := S.pow_dvd_card_of_pow_dvd_card (hd.trans (card_dvd_of_injective f hf))
  have hb : 2 ^ k ≤ 2 ^ 7 := (Nat.le_of_dvd (Nat.card_pos (α := S)) h).trans (small S)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb

private noncomputable def fieldTwoEquiv (F : BinaryField) (h : F.degree = 1) :
    F.Carrier ≃+* ZMod 2 := by
  let : Fintype F.Carrier := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, F.card_eq, h]
    simp)

/-- The binary rank-one field degree is bounded by seven. -/
private theorem linearTwo_degree_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : SL(2,F.Carrier) →* D) (hf : Function.Injective f) :
    F.degree ≤ 7 := by
  apply two_power_le small f hf
  rw [GorensteinWalter.sl2_card_formula, F.card_eq]
  exact dvd_mul_right _ _

/-- The concrete unipotent group bounds degree three without an odd-degree premise. -/
private theorem linearThree_degree_le (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : SL(3,F.Carrier) →* D) (hf : Function.Injective f) :
    F.degree ≤ 2 := by
  have hd := (Matrix.PSL3.LinearThree.unipotentSL F.Carrier).card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.card_unipotentSL, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  omega

/-- Only the binary field can occur for a symplectic four-space embedding. -/
private theorem symplectic_degree_eq_one (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : Matrix.symplecticGroup (Fin 2) F.Carrier →* D)
    (hf : Function.Injective f) : F.degree = 1 := by
  have hd := (Theory.SpecificGroups.SymplecticFour.unipotent (F := F.Carrier)).card_subgroup_dvd_card
  rw [Theory.SpecificGroups.SymplecticFour.card_unipotent, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  have := F.degree_pos
  omega

/-- Only the binary field can occur for a full G₂ embedding. -/
private theorem g2_degree_eq_one (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (F : BinaryField) (f : Atlas.G2.Model F.Carrier →* D)
    (hf : Function.Injective f) : F.degree = 1 := by
  have hd := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
  rw [Atlas.G2.card_unipotent, F.card_eq, ← pow_mul] at hd
  have := two_power_le small f hf hd
  have := F.degree_pos
  omega

/-- The binary SL₅ model already has a two-power divisor 1024. -/
private theorem no_linearFive (small : ∀ S : Sylow 2 D, Nat.card S ≤ 128)
    (f : SL(5,ZMod 2) →* D) (hf : Function.Injective f) : False := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
  norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.prod_univ_zero,
    Fin.val_zero, Fin.val_succ, Nat.mul_one] at h
  have hd : 2 ^ 10 ∣ Nat.card PSL(5,ZMod 2) := by rw [h]; norm_num
  have hd' := hd.trans (card_dvd_of_surjective
    (QuotientGroup.mk' (center SL(5,ZMod 2))) (QuotientGroup.mk'_surjective _))
  have := two_power_le small f hf hd'
  omega

private theorem quasisimple_not_solvable (h : IsQuasisimple A) : ¬ Group.IsSolvable A := by
  let : IsQuasisimple A := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact Group.IsPerfect.not_isSolvable A

private theorem linearTwo_degree_ge_two (h : IsQuasisimple A)
    (F : BinaryField) (e : A ≃* SL(2,F.Carrier)) : 2 ≤ F.degree := by
  by_contra hn
  have hd : F.degree = 1 := by have := F.degree_pos; omega
  let b := e.trans ((Atlas.fieldEquivSL 2 (fieldTwoEquiv F hd)).trans
    SLTwoPermThree.sl2Two_equiv_perm_three.some)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := Group.isSolvable_of_isSolvable_injective
    (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  exact quasisimple_not_solvable h
    (Group.isSolvable_of_isSolvable_injective (f := b.toMonoidHom) b.injective)


/-- The seven marked group families retained by the Sylow bound. -/
inductive Model (A : Type*) [Group A] : Prop
  | linearTwo (F : BinaryField) (lower : 2 ≤ F.degree) (upper : F.degree ≤ 7)
      (equiv : A ≃* SL(2,F.Carrier))
  | linearThree (F : BinaryField) (upper : F.degree ≤ 2) (equiv : A ≃* SL(3,F.Carrier))
  | alternatingSix (equiv : A ≃* alternatingGroup (Fin 6))
  | alternatingSeven (equiv : A ≃* alternatingGroup (Fin 7))
  | tripleSix (centerEquiv : center A ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (A ⧸ center A) ≃* alternatingGroup (Fin 6))
  | g2DerivedTwo (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | linearFourTwo (equiv : A ≃* SL(4,ZMod 2))

private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private noncomputable def alternatingFiveLinearEquiv :
    alternatingGroup (Fin 5) ≃* SL(2,BinaryField.four.Carrier) :=
  (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := BinaryField.four.Carrier) (by
      change Nat.card (GaloisField 2 2) = 4
      rw [GaloisField.card 2 2 (by decide)]
      decide)).some.symm.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm

private noncomputable def alternatingEightLinearEquiv :
    alternatingGroup (Fin 8) ≃* SL(4,ZMod 2) :=
  Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm

variable {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
variable {L J : Subgroup D}
variable {E : Type*} [Group E] [Finite E]

private theorem linear_two (small : ∀ P : Sylow 2 E, Nat.card P ≤ 128)
    (hq : IsQuasisimple E) (F : BinaryField) (e : E ≃* SL(2,F.Carrier)) : Model E :=
  .linearTwo F (linearTwo_degree_ge_two hq F e)
    (linearTwo_degree_le small F e.symm.toMonoidHom e.symm.injective) e

private theorem linear_three (small : ∀ P : Sylow 2 E, Nat.card P ≤ 128)
    (F : BinaryField) (e : E ≃* SL(3,F.Carrier)) : Model E :=
  .linearThree F (linearThree_degree_le small F e.symm.toMonoidHom e.symm.injective) e

private theorem binary_linear (small : ∀ P : Sylow 2 E, Nat.card P ≤ 128)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (e : E ≃* SL(d,ZMod 2)) : Model E := by
  rcases hd with rfl | rfl
  · exact .linearFourTwo e
  · exact (no_linearFive small e.symm.toMonoidHom e.symm.injective).elim

omit [Finite D] in
private theorem irreducible_model (small : ∀ P : Sylow 2 E, Nat.card P ≤ 128)
    (hq : IsQuasisimple E) (e : E ≃* L)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L J) : Model E := by
  cases h with
  | linearTwo F _ a _ _ => exact linear_two small hq F (e.trans a.groupEquiv)
  | linearThree F _ a _ => exact linear_three small F (e.trans a.groupEquiv)
  | symplectic F large _ a _ =>
    have h := symplectic_degree_eq_one small F
      (e.trans a.groupEquiv).symm.toMonoidHom (e.trans a.groupEquiv).symm.injective
    omega
  | symplecticTwo a _ =>
    exact .alternatingSix (e.trans (a.subgroupEquiv.trans binarySymplecticDerivedEquiv))
  | g2 F large _ a _ _ =>
    have h := g2_degree_eq_one small F
      (e.trans a.groupEquiv).symm.toMonoidHom (e.trans a.groupEquiv).symm.injective
    omega
  | g2Two a _ _ => exact .g2DerivedTwo (e.trans a.subgroupEquiv)
  | symmetric n hn a _ _ =>
    rcases hn with rfl | rfl
    · exact linear_two small hq BinaryField.four
        (e.trans (a.subgroupEquiv.trans alternatingFiveLinearEquiv))
    · exact .alternatingSeven (e.trans a.subgroupEquiv)
  | alternatingSix _ a _ _ => exact .alternatingSix (e.trans a.groupEquiv)
  | alternatingSeven _ _ a _ _ _ => exact .alternatingSeven (e.trans a)
  | tripleSix _ a _ =>
    have hc : (center E).map e.toMonoidHom = center L := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact .tripleSix ((centerCongr e).trans a.centerEquiv)
      ((QuotientGroup.congr _ _ e hc).trans a.quotientEquiv)
  | binaryLinear d hd _ a _ => exact binary_linear small hd (e.trans a.groupEquiv)
  | orthogonalSix _ _ a _ _ =>
    exact .linearFourTwo (e.trans (a.groupEquiv.trans alternatingEightLinearEquiv))
  | symmetricEight _ a _ =>
    exact .linearFourTwo (e.trans (a.subgroupEquiv.trans alternatingEightLinearEquiv))
  | exteriorFive _ _ a _ _ _ => exact binary_linear small (Or.inr rfl) (e.trans a)

omit [Finite D] in
/-- Forget the module clauses of the full B.5.1 conclusion while retaining
actual model identifications on the independently specified group. -/
theorem model_of_source (small : ∀ P : Sylow 2 E, Nat.card P ≤ 128)
    (hq : IsQuasisimple E) (e : E ≃* L)
    (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) : Model E := by
  cases h.clause_one with
  | irreducible _ _ _ source _ => exact irreducible_model _ small hq e source
  | doubleThree F _ a _ _ => exact linear_three small F (e.trans a.groupEquiv)
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear small hd (e.trans a.groupEquiv)
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear small hd (e.trans a.groupEquiv)
end SmallModels

variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
/-- Apply the proved B.5 source classifier to the actual C.2.7 star image.
The independent Goldschmidt consumer supplies the displayed Sylow bound. -/
theorem star_small_model_from_source (h : Input KnownSimple.IsKnownSimple H R M K)
    (small : ∀ P : Sylow 2 (starImage K R K), Nat.card P ≤ 128) :
    SmallModels.Model (starImage K R K) := by
  obtain ⟨hLJ, ⟨c⟩⟩ := star_moved_section_from_source h
  let : (K.subgroupOf (K ⊔ R)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  have hq : IsQuasisimple (starImage K R K) := (star_fitting_quasisimple (source_join_input h)).2
  exact SmallModels.model_of_source _ small hq (subgroupOfEquivOfLe hLJ).symm c

end CFSG.Quasithin.ChapterC.C27Source
