module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourExactPathParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoFieldFourApplicationSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalBinaryMarkedSource

/-!
# Exceptional marked selection from an original noncommuting critical pair

The earlier intrinsic center-action theorem constructs the natural alpha
module. Exhaustive beta selection then excludes the small-unitary and
nonlinear rows and restricts the actual beta field to two or four. Applying
the completed field-four recognition and path calculation to this selected
field removes the quotient-model and field-order premises from the marked
exceptional alternative.

Both rows retain the full original endpoint cores and Borel. The binary row
has compatible G₂(2)′ markings for both the full and reduced amalgams; its
path parameters are still a separate obligation. The field-four row retains
the reduced J₂ marking, the original J₂/Aut(J₂) markings and the literal
source extrema r = 6, s = 5. The order-32 beta-core consumer selects this row
without assuming any of those recognition or path conclusions.

The hypothesis `hD` remains the original opposite-core equality defining the
exceptional branch. Neither its discharge nor completion of all Chapter 10
branches is asserted here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.7)--(10.9), printed pp.158--163; original extension markings (15.3),
printed pp.229--231.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open Noncommuting DGS85.Reduction Theory.GroupTheory
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F₀" => reducedFamily L S
local notation "α" => base F₀ false
local notation "β" => base F₀ true

/-- Exhaustive exceptional selection from the original critical pair. -/
theorem original_bTwo_exceptional_marked_selection
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype) :
    let Q₀ := (parabolic L S 0).pCoreIn 2
    let Q₁ := (parabolic L S 1).pCoreIn 2
    (ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 2 ∧
      Nat.card Q₀ = 16 ∧ Nat.card Q₁ = 16 ∧
      (∀ i : Fin 2, enlargedEndpoint L S i = parabolic L S i) ∧
      commonBorel L S = (commonBorel L S).pCoreIn 2 ∧
      Nat.card (commonBorel L S) = 32 ∧
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.originalAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam) ∧
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        Atlas.G2.BinaryParabolicPair.derivedAmalgam)) ∨
    (ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 4 ∧
      Nat.card Q₀ = 64 ∧ Nat.card Q₁ = 32 ∧
      IsExtraspecial 2 Q₁ ∧ Nonempty (Q₁ ≃* MinusExtraspecial.Model) ∧
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        GreenBook.HallJanko.j2Model.toMarking.amalgam) ∧
      (Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
        Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.autJ2Model.toMarking.amalgam)) ∧
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5) := by
  have hab : (graph F₀).Adj α β :=
    ⟨by change false ≠ true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨k,f,fin,ch,alg,c,hactor⟩ :=
    reduced_bTwo_center_action_exists h hc hne hb hab hβu
  have he : alg = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst alg
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hcentral := reduced_bTwo_middle_central h hc hne hb hab hβu
  have hcomm := (reduced_bTwo_center_identities h hc hne hb hab hβu).2.2.2
  have hnot := reduced_graph_core_obstruction h α β hab
  obtain ⟨n,hn,hm,_,hcase⟩ := original_bTwo_exceptional_parabolics_and_core
    h hb c hactor hcentral ht htne hcomm hnot hD (LinearEquiv.refl _ _)
  rcases hcase with ⟨htwo,hQa,hQb,hfull,hB,hcard,_⟩ |
    ⟨hfour,hQa,hQb,hex,hcore⟩
  · have hm2 : ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 2 := by
      simpa only [htwo] using hm
    obtain ⟨K,hK,hfin,hcardK,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcardK)
    exact Or.inl ⟨hm2,hQa,hQb,hfull,hB,hcard,
      original_bTwo_exceptional_binary_iso h hb c hactor hcentral ht htne hcomm hnot
        e hD (LinearEquiv.refl _ _) (hcardK.trans htwo),
      original_bTwo_exceptional_binary_reduced_iso h hb c hactor hcentral ht htne hcomm hnot
        e hD (LinearEquiv.refl _ _) (hcardK.trans htwo)⟩
  · have hm4 : ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 4 := by
      simpa only [hfour] using hm
    obtain ⟨K,hK,hfin,hcard,⟨e⟩⟩ := hm
    let := hK
    let := hfin
    let : Fintype K := Fintype.ofFinite K
    let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact Or.inr ⟨hm4,hQa,hQb,hex,hcore,
      original_bTwo_field_four_reduced_iso h hb c hactor hcentral ht htne hcomm hnot
        e hD (LinearEquiv.refl _ _) (hcard.trans hfour),
      original_bTwo_field_four_marked_parameters h hc hne hb hβu ht htne e
        (hcard.trans hfour) hD⟩

/-- The mixed core-size consumer selects the field-four row without an
assumed field identification or center-action model. -/
theorem original_bTwo_exceptional_core_thirty_two_marked_parameters
    (h : HypothesisF11 L S) {u t : Vertex F₀}
    (hc : IsCriticalPair F₀ α u) (hne : ⁅Z F₀ α,Z F₀ u⁆ ≠ ⊥)
    (hb : b F₀ = 2) (hβu : (graph F₀).Adj β u)
    (ht : (graph F₀).Adj α t) (htne : t ≠ β)
    (hD : (parabolic L S 1).pCoreIn 2 ⊓ (Q F₀ t).map (G₀ L S).subtype =
      (Z F₀ α).map (G₀ L S).subtype)
    (hQ : Nat.card ((parabolic L S 1).pCoreIn 2) = 32) :
    ClassicalGroup.IsPSL (L 1 ⧸ pCore 2 (L 1)) 2 4 ∧
      Nat.card ((parabolic L S 0).pCoreIn 2) = 64 ∧
      IsExtraspecial 2 ((parabolic L S 1).pCoreIn 2) ∧
      Nonempty ((parabolic L S 1).pCoreIn 2 ≃* MinusExtraspecial.Model) ∧
      Nonempty (RankTwoAmalgam.Iso
        (OriginalExtension.reducedAmalgam L S).reverse
        GreenBook.HallJanko.j2Model.toMarking.amalgam) ∧
      (Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.j2Model.toMarking.amalgam) ∨
        Nonempty (RankTwoAmalgam.Iso
          (OriginalExtension.originalAmalgam L S).reverse
          GreenBook.HallJanko.autJ2Model.toMarking.amalgam)) ∧
      HasSourcePathParameters
        (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 6 5 := by
  rcases original_bTwo_exceptional_marked_selection h hc hne hb hβu ht htne hD with
    ⟨_,_,hbinary,_⟩ | ⟨hm,hQa,_,hex,hcore,hred,hiso,hpaths⟩
  · omega
  · exact ⟨hm,hQa,hex,hcore,hred,hiso,hpaths⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile.Reduction
