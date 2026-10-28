module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.SourceSetup
public import CFSG.Quasithin.Chapter1.SourceInputs.KnownSimple
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.GeneralizedFitting.InnerMovingActor

/-!
# The component layer in the original paired-cubic centralizer

The actual A₄ commutator four-group centralizes the odd core by A.1.26.
The original actor, its product with the centralizing involution, also
inverts that core by 1.1.5, forcing the core to vanish. Once the first fixed
involution lies in a component, every other component would centralize the
same actor, contrary to 1.1.5. This identifies the whole layer and its
normality while retaining the original centralizer and actor.

Source: Aschbacher–Smith, the paragraph before 2.4.32 and 2.4.33,
printed pp.547–548. The characteristic-two exclusion and component
absorption remain the separate inputs of 2.4.31 and 2.4.32.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G]

/-- A.1.26 kills the actual odd core because the source central involution
is the product of an element of the commutator four-group and i. -/
theorem source_centralizer_oddCore_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (i : G) (hi : orderOf i = 2)
    (S : Sylow 2 (involutionCentralizer i)) (M : Subgroup G) (z : G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer i) S M z)
    (L U : Subgroup (involutionCentralizer i)) [IsElementaryAbelian 2 U]
    (hL : IsPPerfect 2 L) (hU : ⁅U,L⁆ = U)
    (a : involutionCentralizer i) (ha : a ∈ U) (hz : z = (a : G) * i) :
    pPrimeCore 2 (involutionCentralizer i) = ⊥ := by
  have hsqt : IsStronglyQuasithin (involutionCentralizer i) :=
    (hG.twoLocal_sqtk (isTwoLocal_involution_centralizer hi)).stronglyQuasithin
  have hc : U ≤ centralizer (pPrimeCore 2 (involutionCentralizer i) : Set (involutionCentralizer i)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqt L U hL hU)
  apply bot_unique
  intro u hu
  have hain : (a : G) * (u : G) = (u : G) * (a : G) :=
    (congrArg Subtype.val (hc ha u hu)).symm
  have hii : i * (u : G) = (u : G) * i :=
    (mem_centralizer_singleton_iff.mp u.property).symm
  have hzcomm : z * (u : G) = (u : G) * z := by
    rw [hz]
    exact ((show Commute (a : G) (u : G) from hain).mul_left
      (show Commute i (u : G) from hii)).eq
  have hinv := h.inverts_oddCore u hu
  rw [hzcomm,mul_inv_cancel_right] at hinv
  have hsq : u ^ 2 = 1 := by
    apply Subtype.ext
    change (u : G) ^ 2 = 1
    calc
      (u : G) ^ 2 = (u : G) * (u : G) := pow_two _
      _ = (u : G) * (u : G)⁻¹ := congrArg ((u : G) * ·) hinv
      _ = 1 := mul_inv_cancel _
  have ho : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes
    (pPrimeCore_coprime_card (p := 2) (G := involutionCentralizer i))
    (orderOf_dvd_of_pow_eq_one hsq) ((pPrimeCore 2 (involutionCentralizer i)).orderOf_dvd_natCard hu)
  exact mem_bot.mpr (orderOf_eq_one_iff.mp ho)

/-- The actual centralizer supplies a component with the original marked
catalogue action once the characteristic-two alternative is excluded. -/
theorem source_centralizer_component_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (i : G) (hi : orderOf i = 2)
    (S : Sylow 2 (involutionCentralizer i)) (M : Subgroup G) (z : G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer i) S M z)
    (L U : Subgroup (involutionCentralizer i)) [IsElementaryAbelian 2 U]
    (hL : IsPPerfect 2 L) (hU : ⁅U,L⁆ = U)
    (a : involutionCentralizer i) (ha : a ∈ U) (hz : z = (a : G) * i)
    (hf : generalizedFitting (involutionCentralizer i) ≠ pCore 2 (involutionCentralizer i)) :
    pPrimeCore 2 (involutionCentralizer i) = ⊥ ∧
      ∃ K : Subgroup (involutionCentralizer i), IsComponent (involutionCentralizer i) K ∧
        K.map (involutionCentralizer i).subtype =
          ⁅K.map (involutionCentralizer i).subtype,zpowers z⁆ ∧
        ¬ K.map (involutionCentralizer i).subtype ≤ M ∧
        HasModelAction115 K z := by
  have ho := source_centralizer_oddCore_eq_bot hG i hi S M z h L U hL hU a ha hz
  obtain ⟨K,hK⟩ := exists_component_of_oddCore_eq_bot ho hf
  exact ⟨ho,K,hK,Chapter1.lemma_1_1_5_three_knownSimple hG _ S M z h K hK⟩

/-- Once the first fixed involution lies in K, the original source actor
makes K the entire layer. This proves the normality and 2.4.33 conclusions
without another choice of component or involution. -/
theorem source_component_structure
    (i : G) (S : Sylow 2 (involutionCentralizer i)) (M : Subgroup G) (z : G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer i) S M z)
    (K : Subgroup (involutionCentralizer i)) (hK : IsComponent (involutionCentralizer i) K)
    (a : involutionCentralizer i) (ha : a ∈ K) (hz : z = (a : G) * i)
    (ho : pPrimeCore 2 (involutionCentralizer i) = ⊥) :
    K.Normal ∧ K = componentLayer (involutionCentralizer i) ∧
      generalizedFitting (involutionCentralizer i) = K ⊔ pCore 2 (involutionCentralizer i) := by
  let c : involutionCentralizer i := ⟨i,mem_centralizer_singleton_iff.mpr rfl⟩
  have hc : c ∈ center (involutionCentralizer i) := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp u.property
  let zH : involutionCentralizer i := ⟨z,h.mem_intersection.1⟩
  have he : zH = a*c := Subtype.ext hz
  have hm (D : Subgroup (involutionCentralizer i))
      (hD : IsComponent (involutionCentralizer i) D) : D = ⁅D,zpowers zH⁆ := by
    obtain ⟨_,_,_,_,_,he⟩ := h.component_inputs D hD
    apply map_injective (involutionCentralizer i).subtype_injective
    rw [map_commutator,MonoidHom.map_zpowers]
    exact he
  exact ⟨hK.normal_of_inner_moving_actor zH a c ha hc he hm,
    hK.eq_layer_of_inner_moving_actor zH a c ha hc he hm,
    hK.generalizedFitting_of_inner_moving_actor zH a c ha hc he hm ho⟩

end CFSG.Quasithin.Chapter2.DoubleA3
