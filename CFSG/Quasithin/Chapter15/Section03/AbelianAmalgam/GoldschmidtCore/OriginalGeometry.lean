module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.InitialAssembly
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.Core
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Thompson.Application.Source.Complete
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.WreathTwoResidual
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Source

/-!
# Constructing the terminal geometry from the original local data

The earlier local structure and descent supply the actual line products,
quotients, commutator identities and Thompson control. The compatible
orthogonal action identifies the residual quotient with the order-nine
rotation group. Descent makes its ambient module centralizer a two-group;
the faithful wreath quotient then identifies that centralizer with O₂(M).
These facts instantiate the existing terminal construction, using the
proved F.6.11(1) and B.2.16 producers, to construct the conjugating element
and all four noncentrality clauses of 15.3.68.

The same earlier data also supplies every fusion setup field except the
original 15.3.45(3) fixed-line centralizer bound: source 15.3.2(4) proves
the residual dichotomy, and transport through the actual action kernel
gives its literal ambient join equality. Neither construction uses the
terminal centrality conclusion or an amalgam classification input.

Source: Aschbacher--Smith, 15.3.2(4), 15.3.45(3), and the construction
preceding 15.3.68, printed pp.1121, 1140 and 1154--1155.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
open LocalRelations
open TerminalSourceEndgame.OriginalSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

omit [Finite G] in
private theorem module_normalizer_eq
    (earlier : LocalStructure.EarlierData T M Mc P E) :
    M = normalizer (localModule T M : Set G) := by
  let := standard_elementary earlier.natural
  have hne : localModule T M ≠ ⊥ := by
    intro h
    have he : E = ⊥ := eq_bot_mono earlier.line_le h
    have hc := earlier.line_card
    rw [he, card_bot] at hc
    omega
  exact earlier.ordering.1.1.eq_of_le
    ⟨localModule T M, hne, IsElementaryAbelian.isPGroup 2 _, rfl⟩
    earlier.natural.normalizes

/-- The source 15.3.2(4) dichotomy constructs the fusion setup once the
actual 15.3.45(3) fixed-line centralizer bound is available. -/
theorem earlierFusionInputs_of_fixed_centralizer
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M) :
    FusionCore.EarlierFusionInputs T M (localModule T M) P := by
  let := standard_elementary earlier.natural
  obtain ⟨k⟩ := coordinates_from_standard earlier.natural
    (definite_of_standard earlier.natural earlier.plane_le earlier.plane_card
      earlier.plane_definite)
  refine ⟨module_normalizer_eq earlier, rfl, earlier.module_le, earlier.ordering.1.2,
    earlier.central_fixed, earlier.central_card, ?_, hfixed⟩
  intro X hTX hXM
  rcases source_lemma_15_3_2_4 T k.action earlier.ordering hTX hXM with hsmall | ⟨hfull, hu⟩
  · exact Or.inl hsmall
  · refine Or.inr ⟨?_, hu⟩
    have hpre := congrArg (Subgroup.comap k.action.actor) hfull
    change ((X.subgroupOf M).map k.action.actor).comap k.action.actor =
      (⊤ : Subgroup OrthogonalActor).comap k.action.actor at hpre
    rw [comap_map_eq, comap_top] at hpre
    have hm := congrArg (Subgroup.map M.subtype) hpre
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hXM, k.action.ker_actor,
      subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at hm
    simpa only [inf_comm] using hm

omit [Finite G] in
private theorem residual_quotient_card
    (earlier : LocalStructure.EarlierData T M Mc P E) :
    Nat.card (residualY M Mc ⧸ pCore 2 (residualY M Mc)) = 9 := by
  let Y := residualY M Mc
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  let f := earlier.natural.action.comp (inclusion hYM)
  have hk : f.ker = (centralizer (localModule T M : Set G)).subgroupOf Y := by
    ext y
    change inclusion hYM y ∈ earlier.natural.action.ker ↔ _
    rw [action_ker earlier.natural]
    rfl
  have hcore : f.ker = pCore 2 Y := by
    apply (map_injective Y.subtype_injective)
    rw [hk, subgroupOf_map_subtype, inf_comm]
    exact earlier.residual_core_module.symm
  have hr : f.range = actionImage earlier.natural Y := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_map_of_mem earlier.natural.action y.property
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  let e := (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr (hr.trans earlier.residual_image)).trans
        OrthogonalFourBinary.TerminalLines.residualEquiv.symm))
  rw [Nat.card_congr e.toEquiv]
  norm_num [OrthogonalFourBinary.TerminalLines.RotationCode, Nat.card_prod]

/-- The actual earlier local data and descent construct the terminal geometry. -/
theorem exists_terminal_configuration_from_original
    (earlier : LocalStructure.EarlierData T M Mc P E)
    (descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E) :
    ∃ s ∈ planeStabilizer T P, s ∉ lineT T E ∧
      TerminalConfiguration T M (residualY M Mc) (localModule T M)
        E (otherLine E s) earlier.natural := by
  classical
  let := standard_elementary earlier.natural
  let r := LocalStructure.initialStructure earlier
  have hTM := earlier.ordering.1.2
  have hM := module_normalizer_eq earlier
  obtain ⟨hCT, hMprod, hGEprod, hYN, _, hXq, hYq, hXM, hGEq, hXJ⟩ :=
    Descent.source_descent descent
  obtain ⟨_, hD, _, hdistinct, hZE, _⟩ := Orthogonal.line_sylow_geometry_of_source
    earlier.natural T P E hTM earlier.plane_le earlier.plane_card
    earlier.plane_definite earlier.line_le earlier.line_card earlier.line_singular
    earlier.central_fixed earlier.selected earlier.selected_map
  obtain ⟨hfirst, hVcomm, _, _, _⟩ := Orthogonal.residualY_lineNormalizer_consequences
    earlier.natural Mc T E hTM earlier.line_le earlier.line_card earlier.line_singular
    earlier.residual_image earlier.residual_core_module earlier.selected earlier.selected_map
  obtain ⟨k⟩ := coordinates_from_standard earlier.natural
    (definite_of_standard earlier.natural earlier.plane_le earlier.plane_card
      earlier.plane_definite)
  have hS : (planeStabilizer T P).relIndex (T : Subgroup G) = 2 := by
    obtain ⟨i, hi⟩ := k.plane_eq
    rw [hi]
    exact k.action.planeStabilizer_index_two T hTM i
  have hSD : planeStabilizer T P ≠ lineT T E := by
    intro he
    exact hdistinct (congrArg (actionImage earlier.natural) he.symm)
  have hjoin : residualY M Mc ⊔ (T : Subgroup G) = M := by
    apply le_antisymm (sup_le descent.Y_le_M hTM)
    intro m hm
    change m ∈ (M : Set G) at hm
    rw [hMprod] at hm
    obtain ⟨y, hy, t, ht, rfl⟩ := hm
    exact (residualY M Mc ⊔ (T : Subgroup G)).mul_mem (mem_sup_left hy) (mem_sup_right ht)
  have hkernel : k.action.actor.ker = pCore 2 M := by
    have hp : IsPGroup 2 k.action.actor.ker := by
      apply (T.isPGroup'.comap_subtype (K := M)).to_le
      rw [k.action.ker_actor]
      exact fun _ hx => (hCT.le hx).1
    have he := k.action.actor.comap_pCore_of_ker_isPGroup k.action.onto hp
    rw [Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot] at he
    exact he
  have hcore : twoCoreAmbient (residualY M Mc ⊔ (T : Subgroup G)) =
      centralizer (localModule T M : Set G) := by
    rw [hjoin]
    change (pCore 2 M).map M.subtype = _
    rw [← hkernel, k.action.ker_actor, subgroupOf_map_subtype,
      inf_eq_left.mpr (hCT.le.trans (inf_le_left.trans hTM))]
  have hfour : Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
    let := Orthogonal.singularLine_isKleinFour earlier.natural E
      earlier.line_le earlier.line_card earlier.line_singular
    exact IsKleinFour.nonempty_mulEquiv
  have hBaumann : ChapterB.baumann (lineT T E) ≤
      centralizer (localModule T M : Set G) := r.baumann_le.trans inf_le_right
  have hcomm : lineX E = ⁅lineX E,
      elementaryAbelianMaxJ (centralizer (localModule T M : Set G))⁆ := by
    rwa [← hCT] at hXJ
  obtain ⟨s, hs, hsE, _, c⟩ := exists_terminal_configuration T M Mc
    (residualY M Mc) (localModule T M) (centralizer (localModule T M : Set G)) P E
    earlier.natural hM rfl rfl hCT hMprod
    earlier.plane_le earlier.plane_card earlier.plane_definite
    earlier.line_le earlier.line_card hfour earlier.line_singular earlier.central_card
    hZE hS hD hSD earlier.residual_image hcore (Or.inl (residual_quotient_card earlier))
    hfirst ⟨descent.sylow, descent.sylow_map⟩ hBaumann r.characteristic_control hYN hYq hXq
    hGEq descent.quotientInputs.local_product hGEprod hcomm earlier.ordering.1.1 hXM
    hVcomm.symm (fun _ _ _ h => h.primeToThreeCore_structure)
    Chapter1.RadicalNormalizers.ThompsonSource.source_theoremB216
  exact ⟨s, hs, hsE, c⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
