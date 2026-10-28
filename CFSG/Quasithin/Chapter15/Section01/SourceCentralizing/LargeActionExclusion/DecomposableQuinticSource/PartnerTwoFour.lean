module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableQuinticSource.PartnerTwoEight
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# The exact action on the surviving second four-group

The original prime-five hypothesis makes E₂ a four-group. Its full
normalizer is Mc and fixes the original central line Uc, so the faithful
action has order at most two. The nontrivial displacement [E₂,Mc]=Uc makes
that order exactly two. No marked support line is identified with Uc.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The full normalizer acts on the literal second seed with exact image
order two, and its full pointwise centralizer has index two in Mc. -/
theorem PreparedChosenModule.decomposable_five_partner_two_second_seed_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      (let Z := thompsonPlane T V (c.ambientFactor d s.first).space
       let C := M ⊓ centralizer (Z : Set G)
       letI := caseI_module_centralizer_normal (Z1 := Z) h.normalized
       Nat.card (pResidual 2 (C ⧸
         (M ⊓ centralizer (V : Set G)).subgroupOf C)) = 5) →
      let E₂ := thompsonFixed T V ⊓
        commutatorPreimage (T : Subgroup G) (T : Subgroup G) (localModule T Mc)
      Nat.card E₂.normalizerMonoidHom.range = 2 ∧
        (centralizer (E₂ : Set G)).relIndex Mc = 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hratio hfive hcU hcard E₂
  have hfour := h.decomposable_five_partner_two_second_seed_card_four
    hG T hempty hM hmany hJ hu hne hfull c d hd s π hp hs hdec hratio hfive hcU hcard
  obtain ⟨_, hNE₂, hcomm⟩ := h.decomposable_five_partner_two_second_seed_normalizer
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU
  have hUE₂ := (h.decomposable_five_partner_two_second_seed
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hratio hfive hcU).1.le
  let Uc := localModule T Mc
  have hUcNe : Uc ≠ ⊥ := (one_lt_card_iff_ne_bot Uc).mp (by rw [hcU]; decide)
  have hMcUc : Mc ≤ centralizer (Uc : Set G) := centralizes_of_normalizes_card_two
    hcU (le_normalizer_conjugateSpanBy _ _)
  obtain ⟨u, huNe⟩ := ne_bot_iff_exists_ne_one.mp hUcNe
  let z : E₂ := ⟨u, hUE₂ u.property⟩
  have hz : z ≠ 1 := fun he => huNe
    (Subtype.ext (show (u : G) = 1 from congrArg (fun e : E₂ => (e : G)) he))
  have hfix : ∀ f ∈ E₂.normalizerMonoidHom.range, f z = z := by
    rintro f ⟨g, rfl⟩
    apply Subtype.ext
    change (g : G) * (u : G) * (g : G)⁻¹ = u
    rw [← hMcUc (hNE₂.le g.property) u u.property, mul_inv_cancel_right]
  have hbound : Nat.card E₂.normalizerMonoidHom.range ≤ 2 :=
    card_mulAut_subgroup_le_two_of_fixed_point hfour z hz _ hfix
  have hIne : E₂.normalizerMonoidHom.range ≠ ⊥ := by
    intro he
    have hcentral : Mc ≤ centralizer (E₂ : Set G) := by
      intro x hx
      let n : normalizer (E₂ : Set G) := ⟨x, hNE₂.ge hx⟩
      have hk : n ∈ E₂.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr
        (mem_bot.mp (show E₂.normalizerMonoidHom n ∈ (⊥ : Subgroup (MulAut E₂)) from
          he ▸ (show E₂.normalizerMonoidHom n ∈ E₂.normalizerMonoidHom.range from ⟨n, rfl⟩)))
      rwa [normalizerMonoidHom_ker] at hk
    have hh : ⁅E₂, Mc⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp hcentral)
    exact hUcNe (hcomm.symm.trans hh)
  have hI : Nat.card E₂.normalizerMonoidHom.range = 2 := by
    have hh := (one_lt_card_iff_ne_bot _).mpr hIne
    omega
  refine ⟨hI, ?_⟩
  rw [← hNE₂]
  change ((centralizer (E₂ : Set G)).subgroupOf (normalizer (E₂ : Set G))).index = 2
  rw [← normalizerMonoidHom_ker, index_ker]
  exact hI

end CFSG.Quasithin.Chapter15.Section01
