module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingPair.CubicComponent
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.SpecificGroups.Rudvalis.Model.CubicElementary.Centralizers
public import Theory.SpecificGroups.Rudvalis.Model.Certification
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.SpecificGroups.Rudvalis.Model.Primitive
public import Theory.SpecificGroups.Rudvalis.Multiplier.OddLocal.Three
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Rudvalis
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The native Rudvalis row of the paired alternating-five argument

The actual opposite block supplies a cubic centralizing the selected deleted
module. The component residual theorem places it inside the marked ordinary
component, and the faithful two-core quotient preserves the elementary subgroup
of order sixteen. Native Rudvalis ten-two fixed-point pattern excludes that centralization.

Source: Aschbacher--Smith 2.4.25, printed pp.542--543. All component, quotient,
and module markings are inherited from the original paired-block configuration.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource AlternatingFixedPhi
open Chapter1.XiEmbedding.OuterModels
variable {G : Type*} [Group G] [Finite G]
variable {M M₀ : Subgroup G} {d : MinimalBlockSetup M}

private theorem ru_three_rank_ge_two : 2 ≤ primeRank 3 Rudvalis.Model := by
  by_contra hh
  have hr : primeRank 3 Rudvalis.Model ≤ 1 := by omega
  obtain ⟨P,hc,hna⟩ := Rudvalis.Multiplier.OddLocal.three_subgroup
  obtain ⟨Q,hPQ⟩ := (IsPGroup.of_card hc).exists_le_sylow
  let : IsCyclic Q := Q.isCyclic_of_odd_of_primeRank_le_one (by decide) hr
  exact hna (IsMulCommutative.of_setLike_mul_comm fun x hx y hy =>
    (isMulCommutative_iff_of_setLike.mp (inferInstance : IsMulCommutative Q))
      x (hPQ hx) y (hPQ hy))

private theorem ru_not_commutative : ¬ IsMulCommutative Rudvalis.Model := by
  intro hh
  let : IsMulCommutative Rudvalis.Model := hh
  obtain ⟨P,_,hn⟩ := Rudvalis.Multiplier.OddLocal.three_subgroup
  exact hn inferInstance

private theorem ru_simple : IsSimpleGroup Rudvalis.Model := by
  let : MulAction.IsPreprimitive Rudvalis.Model (Fin 4060) := Rudvalis.model_isPreprimitive
  exact Rudvalis.simple_of_card_of_primitive Rudvalis.model_card

private theorem ru_center_eq_bot : center Rudvalis.Model=⊥ := by
  let : IsSimpleGroup Rudvalis.Model := ru_simple
  rcases (inferInstance : (center Rudvalis.Model).Normal).eq_bot_or_eq_top with hb|ht
  · exact hb
  · exact (ru_not_commutative (center_eq_top_iff.mp ht)).elim

/-- The Rudvalis row for the literal ordinary component of the original Phi normalizer. -/
theorem AlternatingPairSourceSetup.rudvalis_overcomponent_false
    (c : AlternatingPairSourceSetup d M₀)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀)
    (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L := d.block.map d.H.subtype
    let GI := normalizer (Phi S L : Set G)
    ∀ (K : Subgroup GI), IsComponent GI K → L.subgroupOf GI ≤ K →
      SI S L ≤ normalizer (K.map GI.subtype : Set G) →
      Nonempty ((K ⧸ pCore 2 K) ≃* ClassificationModels.SporadicName.ru.Carrier) → False := by
  intro S L GI K hK hLK _ ⟨e⟩
  change (K ⧸ pCore 2 K) ≃* Rudvalis.Model at e
  let : IsSimpleGroup Rudvalis.Model := ru_simple
  let : IsQuasisimple K := hK.2
  let : Group.IsPerfect Rudvalis.Model := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let q : Rudvalis.Model ⧸ center Rudvalis.Model ≃* Rudvalis.Model :=
    (QuotientGroup.quotientMulEquivOfEq ru_center_eq_bot).trans QuotientGroup.quotientBot
  let : IsQuasisimple Rudvalis.Model := {simple := q.isSimpleGroup}
  let : Subsingleton (MulAut.Outer Rudvalis.Model) := rudvalis_outer_subsingleton
  have ho : IsPGroup 2 (MulAut.Outer Rudvalis.Model) := IsPGroup.of_card (n:=0) (by simp)
  exact c.cubic_centralizer_overcomponent_false (D := Rudvalis.Model)
    hG T hM hTM hu hST hSM hMT hi
    ru_center_eq_bot ru_three_rank_ge_two ho
    (fun E hE hc b hb hEB => by
      let : IsElementaryAbelian 2 E := hE
      exact Rudvalis.CubicElementary.not_centralizes_elementary_sixteen E hc b hb hEB)
    K hK hLK ⟨e⟩

end CFSG.Quasithin.Chapter2
