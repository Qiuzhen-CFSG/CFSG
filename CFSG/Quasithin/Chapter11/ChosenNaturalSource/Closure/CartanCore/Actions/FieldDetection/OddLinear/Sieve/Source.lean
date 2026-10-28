module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.RankOne
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.SmallOuter
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Normalizer.RankTwoComponent
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# The remaining full A.3.6 catalogue for a moved Cartan component

Apply completed Theorems A and C to the actual component image in G₁/O₂(G₁),
then compare that image with I/O₂(I) through the intrinsic quotient map.
The constructed Suzuki, PSL₂, PSU₃ and PSL₃ movement arguments exclude
all binary rank-one rows and the binary linear rank-two row. The actual
three-rank bound also excludes alternating groups of degree at least six
and binary linear groups of degrees four and five; A₅ uses its PSL₂(4) marking. The small-outer
calculation excludes the odd-characteristic PSL₂ rows.

The output retains every other simple row and all three nonsimple rows,
with their literal carriers, component clauses and the full A.3.6 common
conclusions. It is a reduction of the source sieve, not its completion.
The remaining cases and 11.5.6 assembly stay with
qt-d-1222-natural-closure-cartan; preceding geometry is discharged by
qt-d-1222-natural-closure.
Source: Aschbacher--Smith A.3.6, pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02 CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.ClassificationModels

/-- The actual Theorem C rows not yet excluded by the field-movement consumers. -/
inductive RemainingSimpleModel (Q : Type*) [Group Q] : Prop
  | three_odd (p : ℕ) (hp : p.Prime) (ho : Odd p) (unitary : Bool)
      (iso : IsPSLSign Q unitary 3 p)
  | rank_two (model : RankTwoTheoremC Q)
      (not_linear : ∀ n : ℕ, 1 ≤ n → ¬ ClassicalGroup.IsPSL Q 3 (2 ^ n))
  | sporadic (name : SporadicName) (hne : name ≠ .j3)
      (iso : Nonempty (Q ≃* name.Carrier))
  | janko_one (iso : Nonempty (Q ≃* Janko1.Model))

/-- Preserve all full-source nonsimple alternatives and their actual models. -/
inductive RemainingA36Alternative {H : Type*} [Group H] [Finite H]
    (B : Subgroup H) : Prop
  | simple (component : IsComponent H B) (simple : IsSimpleGroup B)
      (model : RemainingSimpleModel B)
  | cover (component : IsComponent H B)
      (center : Nonempty (Subgroup.center B ≃* Multiplicative (ZMod 3)))
      (model : ThreeCoverModel B)
  | natural (data : A36Natural B)
  | nilpotent (data : A36Nilpotent B)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CartanActions.FieldDetection.OddLinear
open CFSG.Quasithin.Chapter1.Section02 CFSG.Quasithin.Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : ChosenModule T L V} (E : Geometry D)

/-- Full-source sieve on the actual component image. No catalogue, covering,
field-actor or normalizer-lift premise is assumed. The retained alternatives
are the remaining obligations of the Cartan assembly. -/
theorem moved_component_remaining_source_cases (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (c : LocalGeometry.Coordinates D E.input.field)
    (hcart : LocalGeometry.IsCartan T L E.X)
    (hXR : E.X ≤ normalizer (E.R₁ : Set G))
    (hCX : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁)
    (hz : center (E.L₁ ⧸ pCore 2 E.L₁) = ⊥)
    (hNG : normalizer (T : Set G) ≤ E.M)
    (hr : primeRank 3 E.Y ≤ 1) (hodd : Odd E.input.field.degree)
    {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hmoved : ¬ ⁅I,E.X⁆ ≤ E.Y.pCoreIn 2) :
    let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
    RemainingA36Alternative B ∧ A36Common B ∧ primeRank 3 B ≤ 1 := by
  let B := (I.subgroupOf E.G₁).map (QuotientGroup.mk' (pCore 2 E.G₁))
  have hH : IsSQTK KnownSimple.IsKnownSimple E.G₁ :=
    E.input.source.simpleQTKE.twoLocal_sqtk (D.centralQuotientPreimage_twoLocal E.point hp)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (E.G₁ ⧸ pCore 2 E.G₁) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 E.G₁)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  have hrel := E.component_in_point_normalizer hI
  have hsource : A36Conclusion B := proposition_1_2_1_four_earlier_conclusion
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)) hQ hrel
  let eI : I.subgroupOf E.G₁ ≃* I := subgroupOfEquivOfLe (hI.1.trans E.Y_le_G₁)
  let eQ : (I ⧸ pCore 2 I) ≃* B :=
    (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI)).symm.trans
      (cComponentTwoCoreQuotientEquiv hrel)
  have hrI : primeRank 3 I ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hI.1) (inclusion_injective hI.1)).trans hr
  have hrB : primeRank 3 B ≤ 1 := by
    rw [← primeRank_congr 3 eQ]
    exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hrI
  refine ⟨?_,hsource.2,hrB⟩
  cases hsource.1 with
  | cover hcomp hcenter hmodel => exact .cover hcomp hcenter hmodel
  | natural h => exact .natural h
  | nilpotent h => exact .nilpotent h
  | simple hcomp hsimple hmodel =>
      let : IsSimpleGroup B := hsimple
      let : IsSimpleGroup (I ⧸ pCore 2 I) := eQ.isSimpleGroup
      have hlinear (n : ℕ) (hn : 1 ≤ n)
          (hi : ClassicalGroup.IsPSL B 3 (2 ^ n)) : False := by
        obtain ⟨F,_,_,hF,⟨e⟩⟩ := hi
        let : Fintype F := Fintype.ofFinite F
        let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
          (by simpa only [← Nat.card_eq_fintype_card] using hF)
        let F₀ : BinaryField := {
          Carrier := F
          binaryAlgebra := ZMod.algebra F 2
          degree := n
          degree_pos := hn
          card_eq := hF }
        exact hmoved (E.linearThree_component_commutator_of_marked hp hT hX c hcart
          hXR hCX hz hNG hr hI F₀ (eQ.trans e))
      apply RemainingA36Alternative.simple hcomp hsimple
      cases hmodel with
      | alternating n hn hi =>
          obtain ⟨e⟩ := hi
          have hn5 : n = 5 := by
            by_contra hne
            have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := n) (by omega)
            rw [← primeRank_congr 3 e] at hh
            omega
          subst n
          have hm : ClassificationModels.IsBenderModel (I ⧸ pCore 2 I) :=
            .linear 2 (by decide) ⟨GaloisField 2 2,inferInstance,inferInstance,
              GaloisField.card 2 2 (by decide),
              ⟨eQ.trans (e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm)⟩⟩
          exact (hmoved (E.bender_component_commutator_of_marked hp hT hX c hcart
            hXR hCX hz hNG hr hodd hI hm)).elim
      | linear_odd p n hprime ho hn _hs hi =>
          have hc := E.cartan_coprime_of_local_action hp hX hcart.odd
            (fun _ hprime hdiv => (c.cartan_primeRank hcart hprime hdiv).ge) hCX hz
          exact (hmoved (E.oddLinearTwo_component_commutator hp hX hcart.odd
            (c.cartanTorusEquiv hcart) hc hI hprime ho
            (by rcases hn with rfl | rfl <;> omega) (hi.of_mulEquiv eQ))).elim
      | three_odd p hp ho unitary hi => exact .three_odd p hp ho unitary hi
      | rank_one hi =>
          exact (hmoved (E.bender_component_commutator_of_marked hp hT hX c hcart
            hXR hCX hz hNG hr hodd hI (hi.of_mulEquiv eQ))).elim
      | rank_two hi => exact .rank_two hi hlinear
      | binary_linear n hn hi =>
          obtain ⟨F,_,_,hF,⟨e⟩⟩ := hi
          let : Fintype F := Fintype.ofFinite F
          let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
            simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
          let eB := (e.trans (Atlas.fieldEquivPSL n f)).trans
            (BinaryLinear.OuterCyclic.projectiveEquivSL (by rcases hn with rfl | rfl <;> decide))
          have hh := BinaryLinear.SmallCubicRank.four_or_five hn
          rw [← primeRank_congr 3 eB] at hh
          omega
      | sporadic name hn hi => exact .sporadic name hn hi
      | janko_one hi => exact .janko_one hi
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
