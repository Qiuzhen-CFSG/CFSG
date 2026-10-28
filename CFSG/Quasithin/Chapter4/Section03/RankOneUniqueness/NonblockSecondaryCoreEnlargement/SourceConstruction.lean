module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceImages
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCrossing
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryQuotient

/-!
# Constructing secondary action data from the original marked MS inputs

The selected normal component and the source torus supply all geometric
and action data. The original radical-normalizer theorem supplies the
component-core bound; the original doubled-dual action supplies whole-radical
generation. Strict core enlargement is absent from both construction steps.

The crossing moves the radical image on this same component and quotient.
This constructs source inputs for the outer-action route; it does not yet
identify the quotient model, graph component or full Frattini module.
Source: Aschbacher–Smith, original 4.3.11–16, printed pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- The all-degree source constructor supplies the torus instead of assuming it.
The component, core and normalizer geometry remain explicit earlier-source
inputs of the nonblock assembly owner. Whole-radical generation is derived
through this witness's very same quotient action. -/
theorem MSData.exists_secondaryActionData_of_marked_parabolic
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G)) :
    ∃ s : SecondaryActionData c n, s.component = B ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      ((Q c).subgroupOf (rootNormalizer c)).map s.action ⊔
        ⁅((R₂ c).subgroupOf (rootNormalizer c)).map s.action,
          ((secondary c).subgroupOf (rootNormalizer c)).map s.action⁆ =
        ((R₂ c).subgroupOf (rootNormalizer c)).map s.action := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨_,hmodel,hstrict,haction⟩ := d.secondary_structure_of_marked_parabolic hn D
    hL hSL B hB hBn hsec henlarged (hnorm.trans inf_le_right)
  obtain ⟨Y,hcyc,hcard,hYK,hYr,hfaith,hfix,hsecY,hRY,hmove⟩ :=
    m.exists_source_torus hn D hcore
  let s : SecondaryActionData c n := {
    component := B
    torus := Y
    isComponent := hB
    normal := hBn
    quasisimple := hBq
    secondary_le := hsec
    secondary_lt := hstrict
    secondary_model := hmodel
    torus_le := hYr
    torus_cyclic := hcyc
    torus_card := hcard
    torus_faithful := hfaith
    torus_secondary := hsecY
    torus_normalizes_radical := hRY
    core_eq := hcore
    core_moved := hmove
    radical_le := radical_le_root_normalizer D
    radical_normalizer := hnorm
    enlarged_core_le := henlarged
    radical_action := haction }
  exact ⟨s,rfl,hYK,hfix,s.action_generation_of_generation (m.radical_generation hn D s.core_eq)⟩


/-- Construct the weaker source interface on the actual selected component.
Every premise is among the original marked-MS inputs. -/
theorem MSData.exists_secondaryActionData
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    ∃ s : SecondaryActionData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      EndgameSieve.SecondaryActionData.ActionGeneration s := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨hB,hBn,hsec,_⟩ := d.sourceComponent_spec hn D h hL hSL
  exact d.exists_secondaryActionData_of_marked_parabolic hn D hL hSL
    (d.sourceComponent hn D h hL hSL) hB hBn
    (d.sourceComponent_quasisimple hn D h hL hSL) hsec.le (d.joinCore_eq hn)
    (m.enlarged_core_le_radical_source hn D _
      (sup_le (hsec.le.trans le_sup_left) (inf_le_left.trans le_sup_right)))
    (m.radical_normalizer_source hn D)

/-- The original crossing moves the literal radical image of these data. -/
theorem SecondaryActionData.crossing_moves_radical_image
    (s : SecondaryActionData c n) {d : MSData c n} (m : RootCoordinates d)
    (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V) :
    let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
    (EndgameSieve.SecondaryActionData.radicalImage s).map
      (MulAut.conj (s.action t)).toMonoidHom ≠
        EndgameSieve.SecondaryActionData.radicalImage s := by
  let := s.normal
  exact source_crossing_moves_component_radical_image m hn D s.component
    s.isComponent.perfect s.secondary_le

/-- The source actor and original Sylow image are preserved literally while
its radical image is moved. No involution or field-bit condition is imposed. -/
theorem MSData.exists_secondaryActionData_with_crossing
    (d : MSData c n) (hn : 1 < n) (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier) :
    ∃ s : SecondaryActionData c n,
      s.component = d.sourceComponent hn D h hL hSL ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      EndgameSieve.SecondaryActionData.ActionGeneration s ∧
      let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
      (EndgameSieve.SecondaryActionData.radicalImage s).map
        (MulAut.conj (s.action t)).toMonoidHom ≠
          EndgameSieve.SecondaryActionData.radicalImage s := by
  obtain ⟨s,hs,hY,hfix,hgen⟩ := d.exists_secondaryActionData hn D h hL hSL
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact ⟨s,hs,hY,hfix,hgen,s.crossing_moves_radical_image m hn D⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
