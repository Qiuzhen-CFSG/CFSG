module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionWholeComponent
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionComponentNatural
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionNaturalPlane
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSectionSeedNormalizerSource

/-!
# The original quintic module lies in the partner core when its local module has order four

If the original V escaped the partner two-core, its actual action on F/Uc
would have a normal component moving the entire section. The exact original
half-cost offender identifies that whole action with a binary natural module.
The original marked E/Uc plane has dimension two. Its stabilizer in every
perfect subgroup of this actual section image fixes the plane pointwise,
whereas its stabilizer in a natural special-linear component moves it.
This contradiction proves containment of the original V in O₂(Mc).
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

/-- The original full quintic module is contained in the original partner core
when the partner local module has order four. -/
theorem PreparedChosenModule.decomposable_five_partner_four_le_partner_core
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
      Nat.card (localModule T Mc) = 4 →
      V ≤ Mc.pCoreIn 2 := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  obtain hcore | ⟨heF,ρ,dF,hfaith,hker,hcard,hcore,hsA,hqA,hplane,hmin,hcost,
      hfit,K,hK,hKA,hKN,hnK,hirr,hlist,hNA,hTK,hn,hseed,hwhole,hwholeIrr⟩ :=
    h.decomposable_five_core_or_whole_section_component
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
  · exact hcore
  exfalso
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let F := conjugateSpanBy E C
  let : IsElementaryAbelian 2 F := heF
  let σ := Representation.BinaryOffender.imageRepresentation ρ
  let A := actionSubgroup ρ (V.subgroupOf Mc)
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (Representation.BinaryOffender.actionImage ρ) :=
    ⟨Mc,(Representation.BinaryOffender.actionHom ρ).ker,
      hG.twoLocal_sqtk hMc.1.1,
      QuotientGroup.quotientKerEquivOfSurjective
        (Representation.BinaryOffender.actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective⟩
  obtain ⟨n,hn,⟨e⟩⟩ := DecomposableQuinticControl.whole_component_natural_of_half_cost
    σ hfaith hcore cover hK hmin hKA hcost hplane hwhole
  have hUE : Uc ≤ E := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hdim : Module.finrank (ZMod 2) (dF.imageSpace E) = 2 := by
    apply dF.imageSpace_finrank_of_index E (le_conjugateSpanBy E C) 2
    have hm := (Uc.subgroupOf E).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUE).toEquiv] at hm
    change Uc.relIndex E * Nat.card Uc = Nat.card E at hm
    rw [hcU,s.fixed_card] at hm
    change Uc.relIndex E = 2 ^ 2
    norm_num only [Nat.reducePow]
    omega
  let : IsQuasisimple K := hK.2
  have hfix := h.decomposable_five_partner_four_perfect_seed_stabilizer
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU
    ρ dF K inferInstance
  exact DecomposableQuinticControl.marked_binary_natural_plane_stabilizer_moves
    σ K n e (dF.imageSpace E) hdim hfix

end CFSG.Quasithin.Chapter15.Section01
