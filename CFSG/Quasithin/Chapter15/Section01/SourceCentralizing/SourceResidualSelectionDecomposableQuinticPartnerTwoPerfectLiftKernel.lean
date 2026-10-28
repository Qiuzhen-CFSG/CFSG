module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoThreeNonsolvable
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoPerfectLift
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Full-module control of the actual perfect-lift kernel

On the canonical dimension-three section, the original offender closure is
nonsolvable. Its already constructed perfect lift L therefore moves all of
F and centralizes the literal denominator D. Intersect L with the original
section kernel K. The two-residual of this intersection acts on F with
central displacement in D, so its displacement vanishes. Consequently the
literal conjugation image of K intersect L on the full group F is a two-group.
Both the canonical lift and its exact original section image are retained.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem residual_kernel_centralizes_full_group
    (H F D L : Subgroup G) (hFH : F ≤ H) (hpF : IsPGroup 2 F)
    (hnF : H ≤ normalizer (F : Set G)) (hnD : H ≤ normalizer (D : Set G))
    (hLD : L ≤ centralizer (D : Set G)) :
    let K := commutatorPreimage H F D
    let J := K ⊓ L
    let hn : J ≤ normalizer (F : Set G) :=
      (inf_le_left.trans (commutatorPreimage_le H F D)).trans hnF
    (pResidual 2 J).map J.subtype ≤ centralizer (F : Set G) ∧
      IsPGroup 2 (F.normalizerMonoidHom.comp (Subgroup.inclusion hn)).range := by
  let K := commutatorPreimage H F D
  let J := K ⊓ L
  let B := (pResidual 2 J).map J.subtype
  let hn : J ≤ normalizer (F : Set G) :=
    (inf_le_left.trans (commutatorPreimage_le H F D)).trans hnF
  have hBJ : B ≤ J := map_subtype_le (pResidual 2 J)
  have hBF : B ≤ normalizer (F : Set G) := hBJ.trans hn
  have hBD : B ≤ centralizer (D : Set G) := hBJ.trans (inf_le_right.trans hLD)
  have hFD : ⁅F,B⁆ ≤ D := by
    rw [commutator_comm]
    exact (commutator_mono (hBJ.trans inf_le_left) le_rfl).trans
      (commutator_commutatorPreimage_le H F D hnD)
  have hBC : B ≤ centralizer (F : Set G) := le_centralizer_iff.mp
    (centralizes_of_isPPerfect_central_displacement B F F D
      (isPPerfect_embedded_pResidual 2 J) hpF hBF (hFH.trans hnD)
      (le_centralizer_iff.mp hBD) le_rfl hFD)
  refine ⟨hBC, ?_⟩
  let φ := F.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hk : pResidual 2 J ≤ φ.ker := by
    intro j hj
    change Subgroup.inclusion hn j ∈ F.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hBC (mem_map_of_mem J.subtype hj)
  exact ((pResidual_le_iff_isPGroup_quotient 2 φ.ker).mp hk).of_equiv
    (QuotientGroup.quotientKerEquivRange φ)

/-- The actual canonical perfect lift remains full-moved, while the
section kernel inside it has only a two-group action on all of F. -/
theorem PreparedChosenModule.decomposable_five_partner_two_three_perfect_lift_kernel
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
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          Module.finrank (ZMod 2) (dF.imageSpace E) = 3 →
          let A := actionSubgroup ρ (V.subgroupOf Mc)
          let R := normalClosure (A : Set (Representation.BinaryOffender.actionImage ρ))
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let J := K ⊓ L
          let hn : J ≤ normalizer (F : Set G) :=
            (inf_le_left.trans (commutatorPreimage_le Mc F D)).trans dF.normalized
          Group.IsPerfect L ∧ Mc ≤ normalizer (L : Set G) ∧
            L ≤ conjugateSpanBy V Mc ∧ L ≤ centralizer (D : Set G) ∧
            ⁅F,L⁆ = F ∧ F ≤ L ∧
            actionSubgroup ρ (L.subgroupOf Mc) = (solvableResidual R).map R.subtype ∧
            (pResidual 2 J).map J.subtype ≤ centralizer (F : Set G) ∧
            IsPGroup 2 (F.normalizerMonoidHom.comp (Subgroup.inclusion hn)).range := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hdim
  have hnon := ((h.decomposable_five_partner_two_three_nonsolvable
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hdim
  obtain ⟨hperfect,hnL,hLN,hLD,hFL,hFLle,himage⟩ :=
    (h.decomposable_five_canonical_perfect_lift hG T hempty hM hmany hJ hu hfull
      c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnon
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let : IsElementaryAbelian 2 F := heF
  obtain ⟨hres,himageTwo⟩ := residual_kernel_centralizes_full_group Mc F D L
    dF.section_le (IsElementaryAbelian.isPGroup 2 F) dF.normalized hnD hLD
  exact ⟨hperfect,hnL,hLN,hLD,hFL,hFLle,himage,hres,himageTwo⟩

end CFSG.Quasithin.Chapter15.Section01
