module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoShearSaturation
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelSpan
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoLiftedStabilizer
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoCubicLift
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoNormalizerCubic

/-!
# The original canonical denominator meets both marked planes in lines

In the disjoint branch, the actual original perfect lift covers the full
natural linear actor. Its kernel rows are all shears into the whole literal
denominator. They correct an original moving cubic seed-image stabilizer
to normalize E itself, preserving its canonical action. The original
Thompson seed-normalizer control forbids this cubic movement. Consequently,
outside the original two-core branch, both marked-plane intersections are
lines. All coordinates and shears are constructed from the original source.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine original order-two partner source forces a line of the
canonical denominator in each original marked plane unless V lies in O2(Mc). -/
theorem PreparedChosenModule.decomposable_five_partner_two_core_or_kernel_lines
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
      let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
      let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
      V ≤ Mc.pCoreIn 2 ∨
        (Nat.card (D ⊓ Z₁ : Subgroup G) = 2 ∧ Nat.card (D ⊓ Z₂ : Subgroup G) = 2) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  let Z₁ := thompsonPlane T V (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T V (c.ambientFactor d s.second).space
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  obtain ⟨hcards,hcases,_,_⟩ :=
    (h.decomposable_five_partner_two_seed_intersections.{u,0}
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  rcases hcases with hone | htwo
  · exfalso
    have hDZ : D ⊓ Z₁ = ⊥ := Subgroup.card_eq_one.mp hone
    obtain ⟨_,_,_,_,heF,ρ,dF,_⟩ :=
      (h.decomposable_five_partner_two_core_or_canonical_action
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
    let := heF
    let N := normalClosure (V.subgroupOf Mc : Set Mc)
    let L := ((solvableResidual N).map N.subtype).map Mc.subtype
    let K := commutatorPreimage Mc F D
    let B := K ⊓ N.map Mc.subtype
    have hBF : ⁅B,F⁆ = D :=
      ((h.decomposable_five_partner_two_kernel_span
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF hDZ
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,heD,row,heval,_,_,hsat,_⟩ :=
      ((h.decomposable_five_partner_two_disjoint_saturated_rows
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF hDZ
    let := heD
    have hrow : Function.Surjective row := by
      intro f
      apply (hsat f).mpr
      rw [hBF]
      exact map_subtype_le f.range
    obtain ⟨g,hg,hgD,hgc,hgP,w,hw,hgw⟩ :=
      ((h.decomposable_five_partner_two_cubic_lift
        hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
        ρ dF hDZ
    have hBMc : B ≤ Mc := inf_le_right.trans (map_subtype_le N)
    obtain ⟨b,hbn,hbe⟩ := DecomposableQuinticControl.exists_row_correction_normalizing_subgroup
      Mc F D E B ρ dF (le_conjugateSpanBy E C) hBMc row hrow heval g hgD
      ((subspace_map_eq_iff ρ (dF.imageSpace E) g).mpr hgP)
    let g' : Mc := inclusion hBMc b * g
    have hgc' : ρ (g'^3) = 1 := by
      rw [map_pow,hbe,←map_pow,hgc]
    have hfixed := h.decomposable_five_partner_two_normalizer_cubic_fixed
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU ρ dF g' hbn hgc'
    exact hgw (hbe ▸ hfixed w hw)
  · exact ⟨htwo,hcards.symm.trans htwo⟩

end CFSG.Quasithin.Chapter15.Section01
