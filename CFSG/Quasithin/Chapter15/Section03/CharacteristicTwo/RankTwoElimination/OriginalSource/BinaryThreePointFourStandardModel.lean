module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourSpanEquivalence
public import Theory.Representation.BinaryEndpointInduction.SurvivorAction

/-!
# The standard whole-module action of the actual binary-four component

The exact induced quotient recognition now determines the action of every
element of the original normal component K. Its original subgroup B maps
to the literal endpoint parabolic. The full point quotient and its actual
centralizing kernel are retained in the same packet.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Matrix Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open BinaryEndpointInduction
variable {G : Type*} [Group G] [Finite G]

/-- The whole original point-centralizer span, with every actual component
actor, is the marked natural four-space or exterior six-space. -/
theorem binary_three_source_four_standard_model
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let B := (c.L.subgroupOf C).map q
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    ∃ hW : IsElementaryAbelian 2 W,
      let := hW
      ∃ σ : Representation (ZMod 2) (C ⧸ pCore 2 C) (Additive W),
        (∀ (x : C) (w : Additive W),
          ((σ (q x) w).toMul : G)=x*(w.toMul:G)*(x:G)⁻¹) ∧
        Function.Injective (σ.comp K.subtype) ∧
        σ.ker=centralizer (K : Set (C ⧸ pCore 2 C)) ∧
        ∃ eK : K ≃* SL(4,ZMod 2),
          (B.subgroupOf K).map eK.toMonoidHom=endpointParabolic ∧
          ∃ (dual : Bool)
            (E : Additive W ≃ₗ[ZMod 2] (Fin (if dual then 4 else 6) → ZMod 2)),
            ∀ (k : K) (w : Additive W),
              E (σ k.val w)=E w ᵥ* survivorModelMatrix dual ((eK k)⁻¹) := by
  obtain ⟨hW,σ,hσ,hinj,hker,eK,heK,dual,F,E,hF,hact,hE⟩ :=
    binary_three_source_four_span_equivalence
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  let := hW
  let τ := (σ.comp K.subtype).comp eK.symm.toMonoidHom
  obtain ⟨J,_,hJ⟩ := exists_standard_survivor_equivalence dual τ F hF hact E hE
  refine ⟨hW,σ,hσ,hinj,hker,eK,heK,dual,J,?_⟩
  intro k w
  have hh := hJ (eK k) w
  change J (σ (eK.symm (eK k)).val w)=_ at hh
  rwa [eK.symm_apply_apply] at hh

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
