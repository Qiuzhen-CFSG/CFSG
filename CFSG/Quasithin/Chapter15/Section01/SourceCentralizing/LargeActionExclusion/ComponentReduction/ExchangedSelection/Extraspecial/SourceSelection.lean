module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Extraspecial.Geometry
public import Theory.Representation.ExtraspecialBinarySix.MarkedStabilizer
public import CFSG.Quasithin.ChapterB.Section02.Thompson.Sylow
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonPrepared
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonGeneration
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PGroup.ExtraspecialThreeInvolutionEndpoints
/-!
# Stabilizer construction for a Thompson-compatible extraspecial cubic

Every noncentral cubic generates the actual extraspecial residual together
with the original Sylow action: irreducibility on the Frattini quotient
forces its Sylow orbit to generate. The fixed-plane stabilizer has that
same cubic as its two-residual, and all its two-subgroups have order at
most two, by the faithful six-space calculation.

If this plane is fixed by the original Thompson image, its nontriviality
makes that image the entire Sylow intersection. Its intrinsic normality
in the original Sylow group supplies relative normality after transport.
This constructs every ImageMarking field from a single compatible cubic;
the actual component application is in the parent Extraspecial module.

Existence of a noncentral cubic with the required Thompson-fixed plane
remains a source obligation of qt-e-1515-exchanged-component-selection.
No compatible-cubic existence or later row exclusion is asserted here.
Source: Aschbacher--Smith 15.1.16(c)--18, printed pp.1092--1093.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker
open ChapterD ChapterD.UniqueFactor
variable {D : Type*} [Group D] [Finite D]

private theorem cubic_sup_sylow_of_frattini_irreducible
    (S : Sylow 2 D) [IsExtraspecial 3 (pResidual 2 D)]
    (hI : ChapterD.Section03.FrattiniIrreducible (S : Subgroup D) (pResidual 2 D)
      le_normalizer_of_normal)
    (X : Subgroup (pResidual 2 D)) (hX : Nat.card X = 3)
    (hXZ : X ≠ center (pResidual 2 D)) :
    X.map (pResidual 2 D).subtype ⊔ (S : Subgroup D) = ⊤ := by
  let P := pResidual 2 D
  let H := X.map P.subtype ⊔ (S : Subgroup D)
  let N := P ⊓ H
  let q := QuotientGroup.mk' (frattini P)
  let A := (N.subgroupOf P).map q
  have hXH : X.map P.subtype ≤ H := le_sup_left
  have hSH : (S : Subgroup D) ≤ H := le_sup_right
  have hXP : X ≤ N.subgroupOf P := fun x hx =>
    ⟨x.property,hXH (mem_map_of_mem P.subtype hx)⟩
  have hs : ∀ t : S, ∀ a ∈ A,
      ChapterD.Section03.frattiniAction (S : Subgroup D) P le_normalizer_of_normal t a ∈ A := by
    rintro t a ⟨n,hn,rfl⟩
    refine ⟨MulAut.conjNormal (t : D) n,?_,?_⟩
    · exact ⟨(MulAut.conjNormal (t : D) n).property,
        H.mul_mem (H.mul_mem (hSH t.property) hn.2) (H.inv_mem (hSH t.property))⟩
    · exact (quotientAut_apply_mk (frattini P) (MulAut.conjNormal (t : D)) n).symm
  have hNP : N.subgroupOf P = ⊤ := by
    rcases hI A hs with hb | ht
    · have hn : N.subgroupOf P ≤ frattini P := by
        simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff (N.subgroupOf P)).mp hb
      have hz : X ≤ center P := by
        rw [←IsExtraspecial.frattini_eq_center_three]
        exact hXP.trans hn
      exact (hXZ (eq_of_le_of_card_ge hz (by rw [hX,IsExtraspecial.center_order_p 3 P]))).elim
    · apply frattini_nongenerating
      have hh := congrArg (Subgroup.comap q) ht
      simpa only [A,comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
  have hPH : P ≤ H := (subgroupOf_eq_top.mp hNP).trans inf_le_right
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top S]
  exact sup_le hPH hSH

variable {G : Type*} [Group G] [Finite G]
/-- The original Sylow action and the marked-plane stabilizer generate the action image. -/
theorem source_cubic_stabilizer_generates
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (X : Subgroup (pResidual 2 (internalActionImage M V hn)))
    (hX : Nat.card X = 3) (hXZ : X ≠ center (pResidual 2 (internalActionImage M V hn))) :
    subspaceKernel (imageRepresentation M V hn)
      (fixedSpace (imageRepresentation M V hn) (X.map (pResidual 2 (internalActionImage M V hn)).subtype)) ⊤ ⊔
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict = ⊤ := by
  obtain ⟨_,_,_,hP,_,_,_,hI⟩ := hex
  let := hP
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 (internalActionImage M V hn) :=
    (T.subtype hTM).mapSurjective (f := f) (actionHom M V hn).rangeRestrict_surjective
  have he := cubic_sup_sylow_of_frattini_irreducible S hI X hX hXZ
  apply top_unique
  apply le_trans he.ge
  apply sup_le_sup_right
  rintro x ⟨y,hy,rfl⟩
  exact ⟨mem_top _,fun w hw => hw ⟨y,mem_map_of_mem _ hy⟩⟩

/-- The original Thompson-compatible cubic supplies every image-marking field.
The selection of that cubic remains with the source assembly. -/
theorem imageMarking_of_thompson_fixed_cubic
    (T : Sylow 2 G) {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (hex : SourceCases.Extraspecial (imageRepresentation M V hn)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict))
    (hJne : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict ≠ ⊥)
    (X : Subgroup (pResidual 2 (internalActionImage M V hn)))
    (hX : Nat.card X = 3) (hXZ : X ≠ center (pResidual 2 (internalActionImage M V hn)))
    (hfixed : fixedSpace (imageRepresentation M V hn)
      (X.map (pResidual 2 (internalActionImage M V hn)).subtype) ≤
      fixedSpace (imageRepresentation M V hn)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V hn).rangeRestrict)) :
    ∃ c : ImageMarking T M V hn, c.X = X := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let P := pResidual 2 D
  let f : M →* internalActionImage M V hn := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 (internalActionImage M V hn) :=
    (T.subtype hTM).mapSurjective (f := f) (actionHom M V hn).rangeRestrict_surjective
  let J := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
    (actionHom M V hn).rangeRestrict
  let W := fixedSpace ρ (X.map P.subtype)
  let K := subspaceKernel ρ W ⊤
  have hgen := source_cubic_stabilizer_generates T hTM hn hex X hX hXZ
  obtain ⟨_,_,_,hP,hcard,_,hdim,_⟩ := hex
  let := hP
  have hbound (A : Subgroup D) (hA : IsPGroup 2 A) (hAK : A ≤ K) : Nat.card A ≤ 2 :=
    ExtraspecialBinarySix.noncentral_cubic_stabilizer_two_subgroup_card_le_two
      ρ (imageRepresentation_injective M V hn) P hcard hdim X hX hXZ A hA hAK
  have hJK : J ≤ (S : Subgroup D) ⊓ K := by
    intro j hj
    refine ⟨?_,mem_top _,fun w hw => hfixed hw ⟨j,hj⟩⟩
    exact map_mono (f := (actionHom M V hn).rangeRestrict)
      (subgroupOf_mono M (ChapterB.thompsonJ_le _ _)) hj
  have hJcard : Nat.card J = 2 := by
    have hlo := (one_lt_card_iff_ne_bot J).mpr hJne
    have hhi := (card_le_of_le hJK).trans (hbound _ S.isPGroup'.to_inf_left inf_le_right)
    omega
  have hSK : (S : Subgroup D) ⊓ K = J := by
    apply (eq_of_le_of_card_ge hJK ?_).symm
    exact (hbound _ S.isPGroup'.to_inf_left inf_le_right).trans_eq hJcard.symm
  have hSylow : ∃ Q : Sylow 2 K,
      (Q : Subgroup K).map K.subtype = (S : Subgroup D) ⊓ K := by
    have hp : IsPGroup 2 (((S : Subgroup D) ⊓ K).subgroupOf K) :=
      S.isPGroup'.to_inf_left.comap_subtype
    obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
    have hlo : (S : Subgroup D) ⊓ K ≤ (Q : Subgroup K).map K.subtype := by
      simpa only [map_subgroupOf_eq_of_le (show (S : Subgroup D) ⊓ K ≤ K from inf_le_right)] using
        map_mono (f := K.subtype) hQ
    refine ⟨Q,(eq_of_le_of_card_ge hlo ?_).symm⟩
    rw [hSK]
    exact (hbound _ (Q.isPGroup'.map K.subtype) (map_subtype_le _)).trans_eq hJcard.symm
  have hnormal : (((S : Subgroup D) ⊓ K).subgroupOf S).Normal := by
    rw [hSK]
    apply normal_subgroupOf_of_le_normalizer
    apply le_normalizer_iff.mpr
    rintro s ⟨t,ht,rfl⟩ j ⟨x,hx,rfl⟩
    refine ⟨t*x*t⁻¹,?_,?_⟩
    · exact le_normalizer_iff.mp (ChapterB.le_normalizer_thompsonJ (T : Subgroup G) 1)
        t ht x hx
    · simp only [f,map_mul,map_inv]
      rfl
  exact ⟨{
    X := X
    card_X := hX
    noncentral := hXZ
    fixed_thompson := hfixed
    generates := hgen
    sylow := hSylow
    sylow_normal := hnormal
    residual := ExtraspecialBinarySix.noncentral_cubic_stabilizer_residual
      ρ (imageRepresentation_injective M V hn) hcard hdim X hX hXZ },rfl⟩
end CFSG.Quasithin.Chapter15.Section01.ExtraspecialMarker


namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
open ChapterD ChapterD.UniqueFactor Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The prepared ambient module supplies nontriviality of the original
Thompson image. All remaining marker fields follow from the same cubic's
fixed-space placement. The source selection of that cubic remains open. -/
theorem PreparedChosenModule.extraspecial_imageMarking_of_fixed_cubic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V)
    (hex : letI := h.elementary
      SourceCases.Extraspecial (imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (X : Subgroup (pResidual 2 (internalActionImage M V h.normalized)))
    (hX : Nat.card X = 3)
    (hXZ : X ≠ center (pResidual 2 (internalActionImage M V h.normalized)))
    (hfixed : letI := h.elementary
      fixedSpace (imageRepresentation M V h.normalized)
        (X.map (pResidual 2 (internalActionImage M V h.normalized)).subtype) ≤
      fixedSpace (imageRepresentation M V h.normalized)
        (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
          (actionHom M V h.normalized).rangeRestrict)) :
    letI := h.elementary
    ∃ c : ExtraspecialMarker.ImageMarking T M V h.normalized, c.X = X := by
  let := h.elementary
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  exact ExtraspecialMarker.imageMarking_of_thompson_fixed_cubic T hM.1.2 h.normalized hex
    (chosen_thompson_image_ne_bot _ _ _ hM.1.2 h.normalized hm) X hX hXZ hfixed

end CFSG.Quasithin.Chapter15.Section01
