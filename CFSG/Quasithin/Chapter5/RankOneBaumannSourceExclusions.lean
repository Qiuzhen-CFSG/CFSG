module
public import CFSG.Quasithin.Chapter5.RankOneBaumannSourceSelection
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesG2
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesSymplectic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryModel
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionA5
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule

/-!
# The remaining source branches at the original Baumann scope

The block argument of 4.3.7 uses only 12.2.1, although its existing wrapper
retains 12.2.3. Select the auxiliary homogeneous module internally and reuse
the proved star-action row exclusions at their actual weaker hypotheses.
No ambient rank-two or sporadic exclusion is needed in this branch.

The simultaneous outside choice and quasisimple containing component from
RankOneBaumannSourceSelection consequently leave an ordinary component or
a complete constrained nonblock SourceConfiguration. Both retain the same
original L and the actual full omega-center module, equal to [W,L] under
Baumann escape. The ordinary symplectic marking is also excluded directly by its
nontrivial fixed radical. The exhaustive deleted-five carrier argument now
excludes the actual ordinary component without a component-normalizer identity.
Only the constrained nonblock source contradiction remains here; this module
does not assert the Baumann normalizer bound.

Source: Aschbacher--Smith 4.3.6--8, printed pp.614--616, applied in
5.1.7(1), printed pp.633--634. The star-row assembly follows the checked
Chapter4/Section03/RankOneUniqueness/BlockAlternativesSymplectic.lean proof.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter4 Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter12.Section02 ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
private noncomputable def binarySymplecticDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃*
      alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private noncomputable def binaryFourAlternatingEquiv :
    SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm

/-- The complete source block exclusion under the original Input, with no
chosen-module or later ambient exclusion premise. -/
theorem Input.original_source_block_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K) : False := by
  obtain ⟨U,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  have hn := h.exponent
  have hpsl := h.linear
  obtain ⟨hCJ,s,_,hs⟩ := c.block_star_irreducible_source hf hb
  let e := (subgroupOfEquivOfLe hCJ).symm
  have hseven (a : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≃* alternatingGroup (Fin 7)) : False := by
    obtain ⟨hn2,ha⟩ := c.alternatingSeven_block_of_star_group hn hpsl hf hb a
    exact c.false_of_alternating_block_four D h.original_section1221
      (by simpa [hn2] using hpsl) hf ha
  have hbinary {d : ℕ} (hd : d = 4 ∨ d = 5)
      (a : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype) ≃* SL(d,ZMod 2)) : False := by
    rcases hd with rfl | rfl
    · exact c.block_star_not_alternatingEight hn hpsl hf hb
        (a.trans binaryFourAlternatingEquiv)
    · exact c.block_star_not_linearFiveTwo hn hpsl hf hb a
  cases hs with
  | linearTwo F _ a _ _ =>
    exact c.block_star_not_linearTwo hf F (e.trans a.groupEquiv)
  | linearThree F _ a _ =>
    exact c.false_of_linearThree_source_moved_action D hn hpsl hf hb _ hCJ s F a
  | symplectic F hF _ a _ =>
    exact c.false_of_symplectic_source_moved_action D hf hb _ hCJ s F hF a
  | symplecticTwo a _ =>
    exact c.block_star_not_alternatingSix hf
      ((e.trans a.subgroupEquiv).trans binarySymplecticDerivedEquiv)
  | g2 F hF _ a _ _ =>
    exact c.false_of_g2_model (inferInstance : Finite G) D hf hb hF
      (c.block_model_of_restricted_star_moving hb _ hCJ s (binaryG2 F) a)
  | g2Two a _ _ => exact c.block_star_not_g2DerivedTwo hf (e.trans a.subgroupEquiv)
  | symmetric d hd a _ _ =>
    rcases hd with rfl | rfl
    · exact c.block_star_not_alternatingFive hf (e.trans a.subgroupEquiv)
    · exact hseven (e.trans a.subgroupEquiv)
  | alternatingSix _ a _ _ =>
    exact c.block_star_not_alternatingSix hf (e.trans a.groupEquiv)
  | alternatingSeven _ _ a _ _ _ => exact hseven (e.trans a)
  | orthogonalSix _ _ a _ _ =>
    exact c.block_star_not_alternatingEight hn hpsl hf hb (e.trans a.groupEquiv)
  | symmetricEight _ a _ =>
    exact c.block_star_not_alternatingEight hn hpsl hf hb (e.trans a.subgroupEquiv)
  | binaryLinear d hd _ a _ => exact hbinary hd (e.trans a.groupEquiv)
  | exteriorFive _ _ a _ _ _ => exact hbinary (Or.inr rfl) (e.trans a)
  | tripleSix _ a _ =>
    exact c.block_star_central_not_alternatingSix hf
      ((QuotientGroup.congr _ _ e (by
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          exact (centerCongr e ⟨y,hy⟩).property
        · intro hx
          exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩)).trans
        a.quotientEquiv)


/-- The ordinary symplectic marking is impossible in the original A₅ branch:
its plane radical has a nontrivial central fixed subgroup, whereas [W,L] does not.
Thus this branch needs no later root-normalizer FF argument once its marking
has been constructed from the original C.3.1 source. -/
theorem Input.original_ordinary_symplectic_marking_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (c : SourceConfiguration T L) (m : OrdinarySymplecticMarking c n) : False := by
  have hcore : L.pCoreIn 2 = ⁅W,L⁆ :=
    m.full_module.symm.trans (h.original_fullModule_eq_moved hout)
  have hd : Disjoint (pCore 2 L) (center L) := by
    apply disjoint_def.mpr
    intro x hx hz
    apply Subtype.ext
    apply disjoint_def.mp (h.moved_disjoint_centralizer_of_escape hout)
      (hcore ▸ mem_map_of_mem L.subtype hx)
    intro l hl
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l,hl⟩)
  let B := (L.subgroupOf c.H).subgroupOf c.K
  have hLH : L ≤ c.H := c.le_component.trans (map_subtype_le c.K)
  have hLK : L.subgroupOf c.H ≤ c.K := by
    intro l hl
    obtain ⟨k,hk,he⟩ := c.le_component hl
    exact (Subtype.ext he : k = l) ▸ hk
  let e : L ≃* Theory.SpecificGroups.SymplecticFour.planeLocal (F := m.Field) :=
    ((subgroupOfEquivOfLe hLK).trans (subgroupOfEquivOfLe hLH)).symm.trans
      ((m.componentEquiv.subgroupMap B).trans (MulEquiv.subgroupCongr m.original_local))
  apply Theory.SpecificGroups.SymplecticFour.Plane.radical_inf_center_ne_bot (F := m.Field)
  apply le_bot_iff.mp
  intro x hx
  have hxcore : e.symm x ∈ pCore 2 L := by
    rw [←pCore_map_iso 2 e.symm]
    apply mem_map_of_mem
    rw [Theory.SpecificGroups.SymplecticFour.planeLocal_core_eq m.card h.exponent]
    exact hx.1
  have hxcenter : e.symm x ∈ center L := (centerCongr e.symm ⟨x,hx.2⟩).property
  exact e.symm.map_eq_one_iff.mp (disjoint_def.mp hd hxcore hxcenter)

/-- All source selection and block clauses at the original A₅ Baumann input.
The sharper theorem below also eliminates the ordinary disjunct. -/
theorem Input.original_a5_source_branches_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    IsAlternatingBlock L 5 ∧
    Chapter4.Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ ∧
    (∀ c : SourceConfiguration T L, ¬ Nonempty (OrdinarySymplecticMarking c n)) ∧
    ((∃ (c : OutsideChoice T L) (K : Subgroup c.H),
        IsComponent c.H K ∧ K.Normal ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        L ≤ K.map c.H.subtype ∧ ¬ K.map c.H.subtype ≤ normalizer (L : Set G) ∧
        HypothesisC28 KnownSimple.IsKnownSimple c.H (c.H ⊓ normalizer (L : Set G))
          L (c.intermediate.pCoreIn 2) ⁅W,L⁆ ∧
        (T : Subgroup G) ⊓ c.H < (T : Subgroup G) ∧
        normalizer ((T : Subgroup G) ⊓ c.H : Set G) ≤ normalizer (L : Set G) ∧
        ∃ P : Sylow 2 c.H, (P : Subgroup c.H).map c.H.subtype = (T : Subgroup G) ⊓ c.H) ∨
      ∃ c : SourceConfiguration T L,
        generalizedFitting c.K = pCore 2 c.K ∧ ¬ IsBlock c.K) := by
  obtain ⟨c,K,hb,he,hc,hK,hq,hLK,houtK,hn,hcases,hST,hnS,hS⟩ :=
    h.original_outside_component_of_baumann_escape hout
  refine ⟨hb,he,fun d hm => ?_,?_⟩
  · obtain ⟨m⟩ := hm
    exact h.original_ordinary_symplectic_marking_false hout d m
  · rcases hcases with ho | hf
    · exact Or.inl ⟨c,K,ho,hn,hq,hLK,houtK,hc,hST,hnS,hS⟩
    · obtain ⟨d,_,_,_,hd,_⟩ :=
        h.original_configuration_of_constrained_component c K hK hLK houtK hn hf
      exact Or.inr ⟨d,hd,fun hblock => h.original_source_block_false d hd hblock⟩

/-- The actual ordinary disjunct is impossible at the original Baumann scope.
The chosen module is selected internally; no component-normalizer equality
or later model exclusion is assumed. -/
theorem Input.original_ordinary_component_false
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (c : OutsideChoice T L) (K : Subgroup c.H) (ho : IsComponent c.H K)
    (hLK : L ≤ K.map c.H.subtype)
    (houtK : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) : False := by
  obtain ⟨U,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  exact c.no_ordinary_component_of_alternatingFive D h.original_section1221 h.linear
    (h.alternating_block_of_baumann_escape hout).2.1 K ho hLK houtK

/-- Baumann escape leaves only the constrained nonblock configuration, with
the original L and its full source module. The remaining nonblock argument
belongs to the original Baumann-control assembly. -/
theorem Input.original_nonblock_of_baumann_escape
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G)) :
    IsAlternatingBlock L 5 ∧
    Chapter4.Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2) = ⁅W,L⁆ ∧
    ∃ c : SourceConfiguration T L,
      generalizedFitting c.K = pCore 2 c.K ∧ ¬ IsBlock c.K := by
  obtain ⟨hb,he,_,ho | hc⟩ := h.original_a5_source_branches_of_baumann_escape hout
  · obtain ⟨c,K,hK,_,_,hLK,houtK,_⟩ := ho
    exact (h.original_ordinary_component_false hout c K hK hLK houtK).elim
  · exact ⟨hb,he,hc⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
