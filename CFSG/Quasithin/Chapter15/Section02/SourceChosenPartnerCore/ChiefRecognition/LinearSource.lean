module
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.ChiefRecognition.Linear
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenPartnerCore.RankTwo
public import Theory.Representation.SmallDisplacementParabolics.ModelTransport
public import Theory.Representation.BinaryOffender.SmallRatioTransport
public import CFSG.Quasithin.KnownSimpleSectionTransport

/-!
# Partner-core containment in the linear structural branch

On the actual saturated chief section of L = KcT, the original V-image
supplies a Sylow-central involution of displacement rank two. The full
known-simple SQTK hypothesis and the actual Sylow marking transport to
the automorphism model. Linear recognizes the complete action, including
its outer automorphism. The existing moving-parabolic construction then
uses the nonzero H-fixed image of the source plane to contradict noncore
placement. Thus V lies in O₂(Mc) in either linear structural case.

The final reduction excludes the equal-residual and linear alternatives,
leaving precisely the original conjugate-component row, with its literal
embedded factors, conjugator, set product and quotient models. Its action
recognition and final core-containment assembly remain with the same
qt-e-152-critical-pair owner. The earlier-source premises are 15.2.8,
15.2.11--12 and 15.2.14, from the residual and plane geometry producers;
the chosen-action-contradiction parent retains their final discharge.

Source: Aschbacher--Smith 15.2.27(2), printed p.1119.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor Section01 Section03 ChosenGeometry
open BinaryLinear.OuterCyclic BinaryNaturalDual.ModelOrbits.AutomorphismModel
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

private theorem partner_quotient_sqtk
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS) :
    let L := partnerSpan H Mc ⊔ (T : Subgroup G)
    IsSQTK KnownSimple.IsKnownSimple (L ⧸ pCore 2 L) := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  have hs := source_chosen_partner_join_sqtk h hg
  refine ⟨?_,hs.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 L) pCore_isPGroup).trans
    (hs.stronglyQuasithin p hp ho)

/-- The recognized literal chief action contradicts noncore placement in either linear case. -/
theorem source_chosen_false_of_linear_partner
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hnoncore : ¬ V ≤ twoCoreIn Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ((partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : False := by
  let L := partnerSpan H Mc ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 L)
  obtain ⟨B,U,hc,hU,hB,hσ⟩ := source_chosen_partner_saturated_chief
    h hg hMc hZ hquotient hres hs hnoncore
  have hp : IsPGroup 2 U.val := (isPGroup_pCoreIn 2 Mc).comap_subtype.to_le
    (map_le_iff_le_comap.mp hU)
  let := chief_elementary B U hc hp
  obtain ⟨σ,_,hprop,⟨a,ha,ho,hacent,hr⟩,_,_,_,_,_,_,w,hw,hfix,hHfix⟩ := hσ
  obtain ⟨hf,hi,_,_,_,S,hS,hAS,_,_,_,_,_,_,hq⟩ := hprop
  let j := e.trans (projectiveAutEquiv (by omega : 0 < n))
  let : Finite (MulAut (LinearGroup n)) := Finite.of_equiv _ j.toEquiv
  let τ := σ.comp j.symm.toMonoidHom
  let : IsIrreducible τ :=
    (irreducible_comp_surjective_iff j.symm.toMonoidHom j.symm.surjective σ).mpr hi
  let S' := S.mapSurjective (f := j.toMonoidHom) j.surjective
  have hqaS : q a ∈ S := hAS (mem_map_of_mem q ha)
  have hcent : ∀ s ∈ S, Commute (q a) s := by
    intro s hs
    change s ∈ (S : Subgroup _) at hs
    rw [hS] at hs
    obtain ⟨b,hb,rfl⟩ := hs
    exact hacent b hb
  have hqτ := BinaryOffender.quadraticRatio_comp_equiv_le_two σ j.symm hq
  have hmτ := PartnerChiefRecognition.linear_action_model hn τ
    (IsSQTK.knownSimple_of_equiv j (partner_quotient_sqtk h hg))
    (hf.comp j.symm.injective) hqτ S' (j (q a))
    (mem_map_of_mem j.toMonoidHom hqaS)
    ((j.orderOf_eq (q a)).trans ho)
    (by rintro s ⟨b,hb,rfl⟩; exact (hcent b hb).map j.toMonoidHom)
    ((congrArg (fun x => Module.finrank (ZMod 2) (LinearMap.range (σ x - 1)))
      (j.symm_apply_apply (q a))).trans hr)
  have hm := hmτ.comp_equiv j
  have he : τ.comp j.toMonoidHom = σ := by
    apply MonoidHom.ext
    intro x
    change σ (j.symm (j x)) = σ x
    rw [j.symm_apply_apply]
  rw [he] at hm
  exact source_chosen_false_of_partner_actionModel h hg hMc hplane σ w hw hm hfix hHfix

/-- Original 15.2.27(2) in the linear automorphism structural branch. -/
theorem source_chosen_partner_core_of_linear
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G))
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : ((partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (partnerSpan H Mc ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) : V ≤ twoCoreIn Mc := by
  by_contra hncore
  exact source_chosen_false_of_linear_partner h hg hMc hZ hquotient hres hs hncore hplane hn e

/-- A remaining noncore source lies in the exact conjugate-component alternative. -/
theorem source_chosen_noncore_partner_pair
    {T : Sylow 2 G} {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMc : Mc = centralizer (centralInvolutions T : Set G))
    (hZ : centralInvolutions T ≤ ZS)
    (hquotient : ∀ P ∈ Chapter3.HStar (T : Subgroup G) M,
      Nonempty ((P ⧸ pCore 2 P) ≃*
        RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))))
    (hres : partnerSpan H Mc = threePrimeResidual Mc)
    (hs : StructuralAlternatives T H Mc) (hnoncore : ¬ V ≤ twoCoreIn Mc)
    (hplane : ∀ J ∈ Chapter3.HStar (T : Subgroup G) M,
      residual J ≤ centralizer (ZS : Set G)) :
    ∃ (C : Subgroup G) (t : G),
      C ∈ Chapter1.LStar G (T : Subgroup G) ∧ C ∈ Chapter1.cComponentsIn Mc ∧
      t ∈ (T : Subgroup G) ∧ t ∉ normalizer (C : Set G) ∧
      partnerSpan H Mc = C ⊔ C.conjBy t ∧
      (partnerSpan H Mc : Set G) = (C : Set G) * (C.conjBy t : Set G) ∧
      ((∃ n : ℕ, Even n ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 (2 ^ n)) ∨
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (Chapter1.XiQuotient C) 2 p) := by
  rcases hs with he | ⟨hL,hC,n,hn,hmodel,⟨e⟩⟩ | hpair
  · exact ((source_chosen_noncore_residual_lt h hg hquotient hres hnoncore).ne he.symm).elim
  · exact (source_chosen_false_of_linear_partner h hg hMc hZ hquotient hres
      (Or.inr (Or.inl ⟨hL,hC,n,hn,hmodel,⟨e⟩⟩)) hnoncore hplane hn e).elim
  · exact hpair

end CFSG.Quasithin.Chapter15.Section02
