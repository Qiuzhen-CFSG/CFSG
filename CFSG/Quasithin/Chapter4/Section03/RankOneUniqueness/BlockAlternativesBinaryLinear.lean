module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesBinaryPreparation
public import Theory.SpecificGroups.BinaryLinear.RankOneNormalSections
public import Theory.SpecificGroups.BinaryLinear.FourTwoLocalFive
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.EightKernel

/-!
# The A₈ and SL₅(2) source star exclusions

The original rank-one section has a faithful binary representation in degree
four or five, so its field degree is two. The actual star local contains a
full Sylow of the component and the normal perfect image of the original L.
In A₈, every proper Sylow overgroup is contained in a binary four-space
parabolic, whose order is prime to five. In SL₅(2), the factor five forces an
endpoint parabolic. Its A₈ two-core quotient is incompatible with the normal
perfect image having A₅ two-core quotient.

Both conclusions concern the literal star component. Neither an action marking
nor a parabolic placement is assumed, and the full W stays distinct from V.
They discharge the binary-linear rows of the rank-one block assembly, whose
A₇, symplectic and large G₂ rows remain with this task's assembly owner.
Source: Aschbacher–Smith C.4.1(4), C.4.5 and 4.3.7, pp.151–153,615–616.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem local_core_five (c : SourceConfiguration T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4) :
    Nonempty ((c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    hF
  exact ⟨c.originalLocalCoreEquiv.symm.trans (a.trans b)⟩

private theorem local_five_dvd (c : SourceConfiguration T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4) :
    5 ∣ Nat.card c.componentQuotientL := by
  obtain ⟨a⟩ := local_core_five c hpsl
  have hc : Nat.card (c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) = 60 := by
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact (show 5 ∣ Nat.card (c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) by
    rw [hc]; decide).trans (pCore 2 c.componentQuotientL).card_quotient_dvd_card

private theorem star_local_proper (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) {A : Type*} [Group A]
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≃* A) :
    ((starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.H ⊓ normalizer (L : Set G))).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
          (c.K.map c.H.subtype))).map e.toMonoidHom ≠ ⊤ := by
  intro he
  have hh := map_injective e.injective
    (he.trans (map_top_of_surjective _ e.surjective).symm)
  exact (C27Source.star_thompson_intersection_from_source (c.block_source_input hf)).2.not_ge
    (subgroupOf_eq_top.mp hh)

/-- A₈ cannot be the actual star component in the original rank-one configuration. -/
theorem SourceConfiguration.block_star_not_alternatingEight
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      alternatingGroup (Fin 8)) : False := by
  let e₀ := (e.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two).trans
    (projectiveEquivSL (by decide : 0 < 4))
  have hn2 : n = 2 := by
    have hd := c.binary_linear_degree_bound hn hpsl ((c.block_star_quotientEquiv hb).trans e₀)
    omega
  have hfour : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by simpa [hn2] using hpsl
  let E := e₀.trans (slEquivLinear 4)
  let P := ((starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
    (c.H ⊓ normalizer (L : Set G))).subgroupOf
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype))).map E.toMonoidHom
  let a := (c.block_star_quotientEquiv hb).trans E
  let B := c.componentQuotientL.map a.toMonoidHom
  have hBP : B ≤ P := (c.block_star_local_image hb E).1
  have h5 : 5 ∣ Nat.card P := by
    have h5B : 5 ∣ Nat.card B := by
      rw [card_map_of_injective a.injective]
      exact local_five_dvd c hfour
    exact h5B.trans (card_dvd_of_le hBP)
  obtain ⟨U,hU⟩ := c.block_star_local_sylow
  let S := U.mapSurjective (f := E.toMonoidHom) E.surjective
  have hSP : (S : Subgroup _) ≤ P := map_mono hU
  obtain ⟨W,hW0,hWt,hPW⟩ :=
    ChapterB.ComponentRecognition.SylowOvergroups.exists_invariant_subspace S P hSP
      (star_local_proper c hf E)
  exact BinaryLinear.FourTwoLocalFive.five_not_dvd_parabolic W hW0 hWt
    (h5.trans (card_dvd_of_le hPW))

/-- The SL₅(2) row is excluded using the original normal L-image and full Sylow. -/
theorem SourceConfiguration.block_star_not_linearFiveTwo
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      SL(5,ZMod 2)) : False := by
  have hn2 : n = 2 := by
    have hd := c.binary_linear_degree_bound hn hpsl ((c.block_star_quotientEquiv hb).trans e)
    omega
  have hfour : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4 := by simpa [hn2] using hpsl
  let E := e.trans (slEquivLinear 5)
  let P := ((starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
    (c.H ⊓ normalizer (L : Set G))).subgroupOf
      (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype))).map E.toMonoidHom
  let a := (c.block_star_quotientEquiv hb).trans E
  let B := c.componentQuotientL.map a.toMonoidHom
  have hBP : B ≤ P := (c.block_star_local_image hb E).1
  have hPN : P ≤ normalizer (B : Set _) := (c.block_star_local_image hb E).2
  let f : c.componentQuotientL →* P :=
    (a.toMonoidHom.comp c.componentQuotientL.subtype).codRestrict P
      (fun x => hBP (mem_map_of_mem a.toMonoidHom x.property))
  have hfi : Function.Injective f := by
    intro x y he
    exact Subtype.ext (a.injective (congrArg Subtype.val he))
  have hr : f.range = B.subgroupOf P := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem a.toMonoidHom x.property
    · rintro ⟨z,hz,he⟩
      exact ⟨⟨z,hz⟩,Subtype.ext he⟩
  let : (B.subgroupOf P).Normal := normal_subgroupOf_of_le_normalizer hPN
  let : f.range.Normal := hr.symm ▸ inferInstanceAs (B.subgroupOf P).Normal
  let : Group.IsPerfect c.componentQuotientL := c.componentQuotientL_perfect
  obtain ⟨a5⟩ := local_core_five c hfour
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) := a5.isSimpleGroup
  have hc : Nat.card (c.componentQuotientL ⧸ pCore 2 c.componentQuotientL) = 60 := by
    rw [Nat.card_congr a5.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  obtain ⟨U,hU⟩ := c.block_star_local_sylow
  exact BinaryLinear.RankOneNormalSections.no_normal_sixty_in_five_sylow_overgroup
    (U.mapSurjective (f := E.toMonoidHom) E.surjective) P (map_mono hU) (star_local_proper c hf E) hc f hfi

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
