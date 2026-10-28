module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoFixedLine
public import Theory.GroupTheory.PResidual.ThompsonNormalizer

/-!
# The literal seed normalizer in the order-two partner branch

The full ambient normalizer of E lies in Mc=C_G(Ω₁Z(T)). Thompson
normalizer control transfers the original seed residual to this actual
normalizer. Its Sylow supplement gives N_G(E)=C_G(E) T. In particular the
residual of this normalizer fixes E pointwise. This is a statement about
the literal E; no stabilizer in F/D is lifted to an ambient normalizer.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem PreparedChosenModule.seed_normalizer_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hNC : normalizer (thompsonFixed T V : Set G) ≤
      centralizer (centralInvolutions T : Set G)) :
    let E := thompsonFixed T V
    normalizer (E : Set G) = centralizer (E : Set G) ⊔ (T : Subgroup G) ∧
      (pResidual 2 (normalizer (E : Set G))).map
        (normalizer (E : Set G)).subtype ≤ centralizer (E : Set G) := by
  let E := thompsonFixed T V
  let N := normalizer (E : Set G)
  have hTN : (T : Subgroup G) ≤ N :=
    (le_inf (hM.1.2.trans h.normalized)
      ((ChapterB.le_normalizer_thompsonJ _ _).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hJE : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (E : Set G) :=
    hJ.trans (centralizer_le (show E ≤ localModule T M from inf_le_left.trans h.le_local))
  have hres : (pResidual 2 N).map N.subtype ≤ centralizer (E : Set G) :=
    embedded_pResidual_le_centralizer_of_thompson_normalizer T N M E hTN hM.1.2
      E.le_normalizer le_rfl
      (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1 hJE
      ((embedded_pResidual_mono 2 (inf_le_inf_left M hNC)).trans
        (h.seed_residual.trans (centralizer_le inf_le_left)))
  have hs := congrArg (map N.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTN))
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,
    Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN] at hs
  exact ⟨le_antisymm (hs.symm.le.trans (sup_le_sup hres le_rfl))
    (sup_le (Subgroup.centralizer_le_normalizer _) hTN),hres⟩

/-- The actual order-two partner source identifies the complete ambient seed
normalizer and proves that its residual centralizes the original E. -/
theorem PreparedChosenModule.decomposable_five_partner_two_seed_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      normalizer (E : Set G) = centralizer (E : Set G) ⊔ (T : Subgroup G) ∧
        (pResidual 2 (normalizer (E : Set G))).map
          (normalizer (E : Set G)).subtype ≤ centralizer (E : Set G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain ⟨hEN,_,_⟩ := h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  obtain ⟨_,hMcC,_⟩ := h.decomposable_five_partner_two_fixed_line
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  exact h.seed_normalizer_control hG T hM hJ (hEN.trans_eq hMcC)

end CFSG.Quasithin.Chapter15.Section01
