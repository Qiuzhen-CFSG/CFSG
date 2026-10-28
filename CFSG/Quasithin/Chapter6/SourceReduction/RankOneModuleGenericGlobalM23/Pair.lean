module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Local
public import Theory.GroupTheory.Recognition.QuasithinM23.PairPlacement

/-!
# The original pair stabilizer in the exceptional seven-point quotient

Use the actual quotient map J → J/O₂(J) and the exceptional A₇ equivalence.
The shared core identifies the image of the original K = O²(H) with A₅.
The original T is Sylow in J, so its quotient image is a full Sylow
normalizing that A₅. The seven-point placement theorem gives one pair
fixed pointwise by K and stabilized setwise by KT = H. Taking full
preimages retains the common kernel and the original subgroup inclusions.

This proves source 5.2.11(1), together with the maximality of H in J used
in 5.2.19. The marking is on the literal quotient, not an independent
abstract isomorphism of H. No completion or ambient recognition is asserted.
Source: Aschbacher–Smith 5.2.11 and 5.2.19, printed pp.653–654 and656
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

/-- Source 5.2.11(1): the original H is the setwise pair stabilizer in
one actual seven-point quotient marking of J, and K fixes that same pair
pointwise. In particular H is a maximal proper subgroup of J. -/
theorem Preparation.linear_exceptional_pair_marking
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.LStar G (T : Subgroup G)) (hKJ : residual H < J) :
    ∃ e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7),
      ∃ i j : Fin 7, i ≠ j ∧
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
        (residual H).subgroupOf J =
          (fixingSubgroup (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
        H.subgroupOf J =
          (MulAction.stabilizer (alternatingGroup (Fin 7)) ({i,j} : Set (Fin 7))).comap q ∧
        IsCoatom (H.subgroupOf J) := by
  have hTH := hH.1.1.2
  have hn := (d.block_overcomponent_parameter h hTH hp F hm hF (.inl he) hJ.1 hKJ).1
  have hblock := d.linear_four_overcomponent_exceptional (hn ▸ h) hTH hp F hm hF he hJ.1 hKJ
  obtain ⟨hTJ,hHJ,_⟩ := d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  obtain ⟨hc,_,hb,_⟩ := d.block_overcomponent_quotient h hTH hp F hm hF (.inl he) hJ.1 hKJ.le
  rw [hn] at hb
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hb
  obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
  let eK := a.trans b
  let e := hblock.2.1.some
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  let f : residual H →* alternatingGroup (Fin 7) := q.comp (inclusion hKJ.le)
  have hfk : f.ker = pCore 2 (residual H) := by
    ext x
    change q (inclusion hKJ.le x) = 1 ↔ x ∈ pCore 2 (residual H)
    rw [←MonoidHom.mem_ker,hqker,←mem_map_iff_mem J.subtype_injective,
      ←mem_map_iff_mem (residual H).subtype_injective]
    change (x : G) ∈ J.pCoreIn 2 ↔ (x : G) ∈ (residual H).pCoreIn 2
    rw [hc]
  let N := ((residual H).subgroupOf J).map q
  have hfr : f.range = N := by
    rw [MonoidHom.range_comp, inclusion_range]
  let eN : N ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.subgroupCongr hfr.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hfk).trans eK))
  let S := (T.subtype hTJ).mapSurjective hq
  have hTK : (T : Subgroup G) ≤ normalizer (residual H : Set G) :=
    hTH.trans (le_normalizer_residual H)
  have hSN : (S : Subgroup (alternatingGroup (Fin 7))) ≤ normalizer (N : Set _) := by
    have hSK : (T.subtype hTJ : Subgroup J) ≤ normalizer ((residual H).subgroupOf J : Set J) := by
      rw [Sylow.coe_subtype,←subgroupOf_normalizer_eq hKJ.le]
      exact subgroupOf_mono J hTK
    exact (map_mono hSK).trans (le_normalizer_map q)
  obtain ⟨i,j,hij,hN,hNS⟩ := QuasithinM23.five_and_sylow_pair N eN S hSN
  have hSup : H.subgroupOf J = (residual H).subgroupOf J ⊔ (T.subtype hTJ : Subgroup J) := by
    rw [Sylow.coe_subtype,←subgroupOf_sup hKJ.le hTJ,residual_sup_sylow T H hTH]
  have hmap : (H.subgroupOf J).map q = N ⊔ (S : Subgroup (alternatingGroup (Fin 7))) := by
    rw [hSup,Subgroup.map_sup]
    rfl
  have hkerK : q.ker ≤ (residual H).subgroupOf J := by
    intro x hx
    rw [hqker] at hx
    have hxG : (x : G) ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype hx
    rw [hc] at hxG
    change (x : G) ∈ residual H
    exact map_subtype_le _ hxG
  have hkerH : q.ker ≤ H.subgroupOf J :=
    hkerK.trans (subgroupOf_mono J (map_subtype_le _))
  have hpreK : N.comap q = (residual H).subgroupOf J := comap_map_eq_self hkerK
  have hpreH : (N ⊔ (S : Subgroup (alternatingGroup (Fin 7)))).comap q = H.subgroupOf J := by
    rw [←hmap]
    exact comap_map_eq_self hkerH
  have hmax := Theory.SpecificGroups.Alternating.SevenFivePlacement.sylow_sup_five_isCoatom N eN S hSN
  refine ⟨e,i,j,hij,?_,?_,?_⟩
  · exact hpreK.symm.trans (congrArg (Subgroup.comap q) hN)
  · exact hpreH.symm.trans (congrArg (Subgroup.comap q) hNS)
  · exact hpreH ▸ isCoatom_comap_of_surjective hq hmax

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
