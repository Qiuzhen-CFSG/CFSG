module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.NormalCoreCentralizer
public import Theory.GroupTheory.PGroup.SmallFrattiniFiveRecognition

/-!
# The exact minus core model in the original field-four row

The original marked orbit realizes the square map on five singular
coordinates. Its elementary-rank bound identifies the extraspecial closure
with Q8 * D8. The second theorem transports that concrete model onto both
actual two-cores when the remaining closure-centralizer containment holds.
This is the core-equivalence input to Janko23.HTypeAt, not a local or global
amalgam recognition claim.

Source: Aschbacher–Smith 14.2.16–17 and I.4.7, printed pp.985–987 and 418.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.LocalBinary
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 ChapterE
open Chapter12.Section08
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

theorem source_normal_bender_minus_closure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hm : BenderModel ((H ⊓ M).subgroupOf H) K 2) :
    Nonempty ((conjugateSpanBy (localModule T M) H) ≃* MinusExtraspecial.Model) := by
  let D : ChapterG.Section02.Setup G :=
    { V := localModule T M, V₁ := centralInvolutions T, L := sourceResidual M Mc,
      T := T, H := H }
  obtain ⟨hex,hcenter,hcases⟩ := source_normal_bender_closure_extraspecial
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen 2 hm
  let : IsExtraspecial 2 D.U := hex
  have hUc : Nat.card D.U = 32 := by
    rcases hcases with hh | hh
    · exact hh.2
    · omega
  obtain ⟨_,F,hfield,hfinite,hchar,hF,hmodel⟩ :=
    source_normal_bender_nonabelian_models hG T hempty hM hu hmany hcard e
      H hH hnH hne K hK hqK hgen 2 hm
  let := hfield
  let := hfinite
  let := hchar
  obtain ⟨h,hphi,hphic,w,hw,hfix,hspan,hzero,hpolar⟩ :=
    source_frattini_seed_orbit hG T hempty hM hu hmany hcard e H hH.1 hne
  let := SmallFrattini.quotientElementary h.U_isPGroup
  let ρ := frattiniRepresentation D h.U_isPGroup
  let B := SmallFrattini.quotientBilinearForm h.U_isPGroup hphic
  let Q := SmallFrattini.quotientQuadraticForm h.U_isPGroup hphic
  have hMN : M ≤ normalizer (D.V : Set G) :=
    (InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1).le
  have hfixed (g : H) (hg : g ∈ (H ⊓ M).subgroupOf H) :
      ρ g (Additive.ofMul w) = Additive.ofMul w := by
    change Additive.ofMul (frattiniActor D g w) = Additive.ofMul w
    exact congrArg Additive.ofMul (hfix g (hMN hg.2))
  have hSM : (T.subtype hH.1.1.2 : Subgroup H) ≤ (H ⊓ M).subgroupOf H := by
    intro t ht
    exact ⟨t.property,hM.1.2 ht⟩
  obtain ⟨f,hf,hpull,hcoord⟩ := hmodel.linear_quadratic_realization _ K _ hgen hSM 2 hF
    ρ (Additive.ofMul w) hfixed hspan B
    (SmallFrattini.quotientBilinearForm_isAlt _ _) hpolar
    (fun g x y => SmallFrattini.quotientBilinearForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul y.toMul)
    Q hzero (fun g x => SmallFrattini.quotientQuadraticForm_invariant
      h.U_isPGroup hphic (closureActor D g) x.toMul)
  exact SmallFrattini.minus_model_of_five_quadratic_orbit h.U_isPGroup hphic
    hUc f hpull hcoord

/-- The field-four recognition core on both original carriers, retaining only
 the exact unresolved closure-centralizer containment. -/
theorem source_normal_bender_core_minus_of_centralizer_le
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hnH : 1 < generationParameter H)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (localModule T M) H))
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hm : BenderModel ((H ⊓ M).subgroupOf H) K 2)
    (hC : H.pCoreIn 2 ⊓ centralizer
      (conjugateSpanBy (localModule T M) H : Set G) ≤
        conjugateSpanBy (localModule T M) H) :
    Nonempty (pCore 2 H ≃* MinusExtraspecial.Model) ∧
      Nonempty (pCore 2 K ≃* MinusExtraspecial.Model) := by
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨eU⟩ := source_normal_bender_minus_closure
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen hm
  obtain ⟨hs,_⟩ := source_normal_bender_core_centralizer_reduction
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen 2 hm
  have hQ : H.pCoreIn 2 = U := by
    change U ⊔ (H.pCoreIn 2 ⊓ centralizer (U : Set G)) = H.pCoreIn 2 at hs
    rw [sup_eq_left.mpr hC] at hs
    exact hs.symm
  obtain ⟨hUK,hKQ,_⟩ := source_normal_bender_component_core_split
    hG T hempty hM hu hmany hcard e H hH hnH hne K hK hqK hgen 2 hm
  have hQK : (K.pCoreIn 2).map H.subtype = U :=
    le_antisymm (hKQ.trans_eq hQ) hUK
  let eH := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let eK := (pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective
  let eKH := (K.pCoreIn 2).equivMapOfInjective H.subtype H.subtype_injective
  exact ⟨⟨eH.trans ((MulEquiv.subgroupCongr hQ).trans eU)⟩,
    ⟨eK.trans (eKH.trans ((MulEquiv.subgroupCongr hQK).trans eU))⟩⟩
end CFSG.Quasithin.Chapter14.Section02.LocalBinary
