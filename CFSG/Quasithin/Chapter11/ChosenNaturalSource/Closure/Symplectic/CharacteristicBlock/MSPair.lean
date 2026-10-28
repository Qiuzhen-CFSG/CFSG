module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock.OddIndex
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointBlocks.Conditions
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# The original full-image symplectic MS-pair

Put Q₁ = O₂(G₁). The group LQ₁ is normal in LT, so characteristic two
passes from LT to LQ₁. It lies in the two-local normalizer of the original
chosen V and is therefore SQTK. The original component remains a relative
C-component of LQ₁; the marked action identifies its actual O₂-quotient
with Sp₄ over the original nonbinary field.

Together with the odd-index subgroup (L₁T) ∩ LQ₁ and the exclusion of
normal characteristic subgroups of Q₁, this proves every clause of the
existing NonbinaryMSPair interface for LQ₁ in the full-image branch.
The source application obtains the core containment and action-image
alternative from the preceding radical and opposite-pair arguments.

This establishes the input to C.1.32, not its classification conclusion.
The root-image exclusion and Sp₄(4)-block recognition, followed by the
already checked BlockClosure application, remain with
qt-d-1222-natural-closure-sp4.

Source: Aschbacher--Smith 11.5.7, printed p.783; C.1.31, printed p.135.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open RadicalAction
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The original Sylow normalizes both factors of LQ₁. -/
theorem core_join_normalizes (m : MarkedFlag E) :
    L ⊔ (T : Subgroup G) ≤ normalizer ((L ⊔ E.G₁.pCoreIn 2 : Subgroup G) : Set G) := by
  apply sup_le
  · exact le_sup_left.trans (L ⊔ E.G₁.pCoreIn 2).le_normalizer
  · exact (le_inf D.sylow_normalizes_component
      (m.sylow_le_point_normalizer.trans (point_normalizer_normalizes_core E))).trans
        (normalizer_inf_normalizer_le_normalizer_sup L (E.G₁.pCoreIn 2))

/-- Normality is relative to LT, not to the ambient simple group. -/
theorem core_join_normal (m : MarkedFlag E) :
    ((L ⊔ E.G₁.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
  normal_subgroupOf_of_le_normalizer (core_join_normalizes E m)

/-- Characteristic two descends from LT to its normal subgroup LQ₁. -/
theorem core_join_characteristicTwo (m : MarkedFlag E) :
    generalizedFitting (L ⊔ E.G₁.pCoreIn 2 : Subgroup G) =
      pCore 2 (L ⊔ E.G₁.pCoreIn 2 : Subgroup G) := by
  have hc : HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
      (E.input.source.simpleQTKE.evenCharacteristic T)
      ⟨E.input.source.maximal_faithful.1.1.2.2, fun _ hx => mem_sup_right hx⟩)
  let := core_join_normal E m
  have hh := normal_core_selfCentralizing hc
    ((L ⊔ E.G₁.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G)))
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (sup_le le_sup_left
      ((core_le_sylow E m).trans le_sup_right)))).mp hh

/-- The original component remains a C-component in the intermediate group LQ₁. -/
theorem core_join_component (m : MarkedFlag E) :
    (L.subgroupOf (L ⊔ E.G₁.pCoreIn 2)).IsCComponent :=
  E.input.source.maximal_faithful.1.1.1.subgroupOf_of_le le_sup_left
    (sup_le le_sup_left ((core_le_sylow E m).trans le_sup_right))

/-- The original nontrivial elementary abelian V places LQ₁ in a two-local SQTK group. -/
theorem core_join_sqtk (m : MarkedFlag E) :
    IsSQTK KnownSimple.IsKnownSimple (L ⊔ E.G₁.pCoreIn 2 : Subgroup G) := by
  have hn : L ⊔ E.G₁.pCoreIn 2 ≤ normalizer (V : Set G) :=
    sup_le D.normalizes ((core_le_sylow E m).trans E.input.sylow_normalizes)
  have ht : IsTwoLocal (normalizer (V : Set G)) := by
    let := D.elementary
    exact ⟨V, D.ne_bot, IsElementaryAbelian.isPGroup 2 V, rfl⟩
  have hq := (E.input.source.simpleQTKE.twoLocal_sqtk ht).subgroup
    ((L ⊔ E.G₁.pCoreIn 2).subgroupOf _)
  exact ⟨hq.stronglyQuasithin.of_injective
    (subgroupOfEquivOfLe hn).symm.toMonoidHom (subgroupOfEquivOfLe hn).symm.injective,
    hq.isKGroup.of_injective (subgroupOfEquivOfLe hn).symm.toMonoidHom
      (subgroupOfEquivOfLe hn).symm.injective⟩

/-- The literal product decomposition LQ₁ uses normalization of L by Q₁. -/
theorem core_join_product (m : MarkedFlag E) :
    ∀ x ∈ L ⊔ E.G₁.pCoreIn 2,
      ∃ l ∈ L, ∃ q ∈ E.G₁.pCoreIn 2, l*q=x := by
  intro x hx
  have hn := (core_le_sylow E m).trans D.sylow_normalizes_component
  have hh : x ∈ (L : Set G) * (E.G₁.pCoreIn 2 : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left L _ hn]
    exact hx
  exact hh

open LocalGeometry.Normalizers.PointBlocks
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

/-- All C.1.31 inputs for the actual full-image subgroup LQ₁, with its marked symplectic quotient. -/
theorem full_image_msPair (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hcore : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2)
    (hfull : actionImage (V := V) (E.G₁.pCoreIn 2) = actionImage (V := V) E.R₁) :
    NonbinaryMSPair E.input.field L (E.G₁.pCoreIn 2) := by
  refine ⟨E.input.nonbinary, core_join_sqtk E m, core_join_characteristicTwo E m,
    core_join_product E m, core_join_component E m,
    Or.inr (Or.inl ⟨m.action.groupEquiv⟩), ?_, ?_⟩
  · obtain ⟨H,hH,hodd,hHQ⟩ := msOddIndexRadical_of_full_image E m g hpoint hout hcore hfull
    let J := L ⊔ E.G₁.pCoreIn 2
    refine ⟨H.map J.subtype, ?_, ?_, ?_⟩
    · exact lt_of_le_of_ne (map_subtype_le H) (by
        intro he
        apply hH.ne
        apply map_injective J.subtype_injective
        simpa only [← MonoidHom.range_eq_map,range_subtype] using he)
    · change Odd ((H.map J.subtype).subgroupOf J).index
      simpa only [subgroupOf_map_subtype_eq] using hodd
    · have hh := congrArg (map J.subtype) hHQ
      rw [map_subgroupOf_eq_of_le (show E.G₁.pCoreIn 2 ≤ J from le_sup_right)] at hh
      change (H.pCoreIn 2).map J.subtype = E.G₁.pCoreIn 2 at hh
      rw [map_pCoreIn_of_injective 2 H J.subtype J.subtype_injective] at hh
      exact hh
  · intro C hC hn
    let := hC
    by_contra hne
    apply characteristic_not_normalized E m hout C hne
    exact le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
      ((map_subtype_le C).trans le_sup_right)).mp hn)

/-- The preceding source inputs leave exactly the root-image branch or a genuine nonbinary MS-pair. -/
theorem msPair_reduction_of_preceding (m : MarkedFlag E)
    (g : Sp E.input.field.Carrier)
    (hpoint : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hcartan : PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj g).toMonoidHom)
    (hn3 : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.V₃ : Set G))
    (hirr : ∀ A : Subgroup G, E.V₁ ≤ A → A ≤ E.V₃ →
      E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) → A = E.V₁ ∨ A = E.V₃)
    (hti : ∀ x ∈ E.M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) (hVX : ⁅V,E.X⁆ = V)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hout : ¬ centralizer (E.V₁ : Set G) ≤ E.M)
    (hne : ¬ IsMulCommutative E.W) :
    V ≤ E.G₁.pCoreIn 2 ∧ E.W ≤ E.G₁.pCoreIn 2 ∧ IsMulCommutative E.U ∧
      L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 ∧
      (actionImage (V := V) (E.G₁.pCoreIn 2) =
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype ∨
       NonbinaryMSPair E.input.field L (E.G₁.pCoreIn 2)) := by
  obtain ⟨hV,hW,hU,hcore,_,himage⟩ := characteristic_reduction_of_preceding E m g
    hpoint hthree hX hcartan hn3 hirr hti hgen hVX hfour hfive hout hne
  refine ⟨hV,hW,hU,hcore,?_⟩
  rcases himage with hr | ⟨hf,_⟩
  · exact Or.inl hr
  · exact Or.inr (full_image_msPair E m g hpoint hout hcore hf)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.CharacteristicBlock
