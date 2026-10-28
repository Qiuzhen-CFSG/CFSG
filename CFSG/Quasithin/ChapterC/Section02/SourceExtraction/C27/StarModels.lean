module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SourceRanks
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The full group catalogue and central kernel of the C.2.7 star component

The proved B.5.1 moved-section classifier supplies every group model of K*.
This extraction retains all binary field sizes, the large symplectic and G₂
families, the small derived groups, A₅–A₈, SL₅(2), and the literal triple
cover of A₆ with its cubic center. No independent Sylow-order bound is used.

For the actual map K → K*, C.2.7(1) makes the induced kernel on K/O₂(K)
central. The complete A.3.6 source theorem bounds that quotient's center by
one or three. Thus the original star map has solvable kernel of order prime
to five, retaining the marked five-residual in the Chapter 15 application.

Source: Aschbacher–Smith, C.2.7(1–3), pp.145–147; B.5.1, pp.99–103;
A.3.6, pp.43–45; original 15.2.4, pp.1106–1107.
-/

public section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ProjectiveLine
namespace StarModels
universe u v w
variable {D : Type u} [Group D] [Finite D]
variable {A : Type v} [Group A]

/-- The complete group-family projection of the actual B.5.1 conclusion. -/
inductive Model (A : Type*) [Group A] : Prop
  | linearTwo (F : BinaryField) (equiv : A ≃* SL(2,F.Carrier))
  | linearThree (F : BinaryField) (equiv : A ≃* SL(3,F.Carrier))
  | symplectic (F : BinaryField) (large : 1 < F.degree)
      (equiv : A ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
  | g2 (F : BinaryField) (large : 1 < F.degree) (equiv : A ≃* Atlas.G2.Model F.Carrier)
  | g2DerivedTwo (equiv : A ≃* commutator (Atlas.G2.Model (ZMod 2)))
  | alternating (n : ℕ) (degree : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8)
      (equiv : A ≃* alternatingGroup (Fin n))
  | linearFiveTwo (equiv : A ≃* SL(5,ZMod 2))
  | tripleSix (centerEquiv : center A ≃* Multiplicative (ZMod 3))
      (quotientEquiv : (A ⧸ center A) ≃* alternatingGroup (Fin 6))

private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private noncomputable def binaryFourAlternatingEquiv :
    SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm

variable {V : Type w} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
variable {L J : Subgroup D}
variable {E : Type*} [Group E]

private theorem binary_linear {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : E ≃* SL(d,ZMod 2)) : Model E := by
  rcases hd with rfl | rfl
  · exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans binaryFourAlternatingEquiv)
  · exact .linearFiveTwo e

omit [Finite D] in
private theorem irreducible_model (e : E ≃* L)
    (h : ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L J) : Model E := by
  cases h with
  | linearTwo F _ a _ _ => exact .linearTwo F (e.trans a.groupEquiv)
  | linearThree F _ a _ => exact .linearThree F (e.trans a.groupEquiv)
  | symplectic F large _ a _ => exact .symplectic F large (e.trans a.groupEquiv)
  | symplecticTwo a _ =>
    exact .alternating 6 (Or.inr (Or.inl rfl)) (e.trans (a.subgroupEquiv.trans binarySymplecticDerivedEquiv))
  | g2 F large _ a _ _ => exact .g2 F large (e.trans a.groupEquiv)
  | g2Two a _ _ => exact .g2DerivedTwo (e.trans a.subgroupEquiv)
  | symmetric n hn a _ _ =>
    apply Model.alternating n _ (e.trans a.subgroupEquiv)
    rcases hn with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
  | alternatingSix _ a _ _ => exact .alternating 6 (Or.inr (Or.inl rfl)) (e.trans a.groupEquiv)
  | alternatingSeven _ _ a _ _ _ => exact .alternating 7 (Or.inr (Or.inr (Or.inl rfl))) (e.trans a)
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
  | binaryLinear d hd _ a _ => exact binary_linear hd (e.trans a.groupEquiv)
  | orthogonalSix _ _ a _ _ =>
    exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans a.groupEquiv)
  | symmetricEight _ a _ =>
    exact .alternating 8 (Or.inr (Or.inr (Or.inr rfl))) (e.trans a.subgroupEquiv)
  | exteriorFive _ _ a _ _ _ => exact .linearFiveTwo (e.trans a)

omit [Finite D] in
/-- Forget only the module clauses, retaining actual group identifications. -/
theorem model_of_source (e : E ≃* L) (h : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L) : Model E := by
  cases h.clause_one with
  | irreducible _ _ _ source _ => exact irreducible_model _ e source
  | doubleThree F _ a _ _ => exact .linearThree F (e.trans a.groupEquiv)
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear hd (e.trans a.groupEquiv)
  | repeatedNatural d r hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact binary_linear hd (e.trans a.groupEquiv)
end StarModels

variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}
/-- Apply the full model extraction to the original C.2.7 star component. -/
theorem star_model_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    StarModels.Model (starImage K R K) := by
  obtain ⟨hLJ, ⟨c⟩⟩ := star_moved_section_from_source h
  exact StarModels.model_of_source _ (subgroupOfEquivOfLe hLJ).symm c

/-- A.3.6 bounds the center of the literal source two-core quotient. -/
theorem coreQuotient_center_card_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    Nat.card (center (K ⧸ pCore 2 K)) = 1 ∨ Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
  let Q := K ⧸ pCore 2 K
  let : IsQuasisimple Q := h.quasisimple
  have hKsq : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.component.1)).mp (h.setup.sqtk.subgroup (K.subgroupOf H))
  have hQsq : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_, hKsq.isKGroup.quotient (pCore 2 K)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 K) pCore_isPGroup).trans
      (hKsq.stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup Q).IsCComponent :=
    (show IsComponent Q ⊤ from ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hc := (ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    Q hQsq (pCore_quotient_pCore_eq_bot 2) ⊤ htop).2
  let : IsQuasisimple (⊤ : Subgroup Q) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hh := ChapterA.SQTKStructure.NonnormalOuterSource.FourModels.center_card_of_common hc
  simpa only [Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv] using hh

/-- The original C.2.7 kernel bound gives the actual central comparison map. -/
theorem coreToStar_ker_central_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    (coreToStar h.normalizes).ker ≤ center (K ⧸ pCore 2 K) :=
  coreToStar_ker_le_center_of_bound h.normalizes (kernel_offender_from_source h).1.upper

/-- No factor of five is lost in the central comparison. -/
theorem coreToStar_ker_not_five_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    ¬5 ∣ Nat.card (coreToStar h.normalizes).ker := by
  intro hf
  have hh := hf.trans (card_dvd_of_le (coreToStar_ker_central_from_source h))
  rcases coreQuotient_center_card_from_source h with hc | hc <;> rw [hc] at hh <;> norm_num at hh

/-- The actual component map retains the factor of five. -/
theorem toStarImage_ker_not_five_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    ¬5 ∣ Nat.card (toStarImage K R).ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hf
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := (toStarImage K R).ker) 5 hf
  let π := QuotientGroup.mk' (pCore 2 K)
  let y : (coreToStar h.normalizes).ker := ⟨π x.val, by
    change coreToStar h.normalizes (π x.val) = 1
    rw [coreToStar_mk]
    exact x.property⟩
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have ho : orderOf (x : K) = 5 := (Subgroup.orderOf_coe x).trans hx
  have hy : orderOf y = 5 := by
    rw [←Subgroup.orderOf_coe y]
    change orderOf (π x.val) = 5
    rw [π.orderOf_map_eq_of_coprime_of_isPGroup_ker hπker _ (by rw [ho]; decide),ho]
  exact coreToStar_ker_not_five_from_source h (hy ▸ orderOf_dvd_natCard y)

/-- The preimage of the remaining central kernel is solvable. -/
theorem toStarImage_ker_solvable_from_source (h : Input KnownSimple.IsKnownSimple H R M K) :
    Group.IsSolvable (toStarImage K R).ker := by
  let N := (toStarImage K R).ker
  let π := QuotientGroup.mk' (pCore 2 K)
  let f : N →* center (K ⧸ pCore 2 K) := (π.comp N.subtype).codRestrict _ (by
    intro x
    apply coreToStar_ker_central_from_source h
    change coreToStar h.normalizes (π x.val) = 1
    rw [coreToStar_mk]
    exact x.property)
  have hfker : f.ker = (pCore 2 K).comap N.subtype := by
    ext x
    change (⟨π x.val, _⟩ : center (K ⧸ pCore 2 K)) = 1 ↔ x.val ∈ pCore 2 K
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.val
  have hp : IsPGroup 2 f.ker := by
    rw [hfker]
    exact pCore_isPGroup.comap_of_injective N.subtype N.subtype_injective
  let : Group.IsNilpotent f.ker := hp.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

end CFSG.Quasithin.ChapterC.C27Source
