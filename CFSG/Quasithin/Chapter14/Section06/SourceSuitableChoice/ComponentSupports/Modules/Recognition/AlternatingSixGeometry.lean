module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleLinearThree
public import CFSG.Quasithin.ChapterD.Section02.AlternatingSixTypes
public import Theory.Representation.BinaryOffender.AlternatingSixCentralCover
public import Theory.Representation.BinaryOffender.Homogeneous.AlternatingSixInertia
public import Theory.SpecificGroups.AlternatingSix.NaturalCubicGeneration
public import Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.Overgroups

/-!
# The literal A₆ support normalizer geometry

The source parabolic swap is outside natural S₆ in Aut(A₆). Exact inertia
of the homogeneous central cover therefore gives [T:N_T(W)]=2. The
self-normalizing component Sylow and Mc=KT then give Mc ∩ N(N_T(W))=T.
The original support lies in the required fitting preimage and its distinct
conjugates intersect only in the component-fixed space. No splitting or
fixed-free assertion is imposed on the five-dimensional cover.

Source: Aschbacher--Smith14.6.22--24, printed pp.1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
variable {G : Type*} [Group G] [Finite G]

private theorem swap_not_natural
    (P : Sylow 2 (alternatingGroup (Fin 6))) (J L : Subgroup (alternatingGroup (Fin 6)))
    (hi : J ⊓ L = (P : Subgroup (alternatingGroup (Fin 6)))) (hne : J ≠ L)
    (hall : ∀ N : Subgroup (alternatingGroup (Fin 6)), IsCoatom N →
      ((P : Subgroup (alternatingGroup (Fin 6))) ≤ N ↔ N = J ∨ N = L))
    (α : MulAut (alternatingGroup (Fin 6)))
    (hJ : J.map α.toMonoidHom = L) (hL : L.map α.toMonoidHom = J) :
    α ∉ AlternatingSix.ShadowLocal.natural := by
  intro hα
  have hp : (P : Subgroup (alternatingGroup (Fin 6))).map α.toMonoidHom = P := by
    rw [←hi,map_inf _ _ _ α.injective,hJ,hL,inf_comm]
  obtain ⟨B,C,hPB,_,hiB,_,_,hfix⟩ := AlternatingSix.NaturalCubicGeneration.invariant_cubic_pair P
  have hbcard : Nat.card B = 24 := by
    have hh := relIndex_mul_card_of_le hPB
    rw [hiB,AlternatingSix.ShadowLocal.alternatingSylow_card] at hh
    exact hh.symm
  have hbtop : B ≠ ⊤ := by
    intro hh
    rw [hh,Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup (alternatingGroup (Fin 6))) ≃* alternatingGroup (Fin 6)).toEquiv,
      AlternatingSix.ShadowLocal.card_A6] at hbcard
    contradiction
  have hBP : B ≠ (P : Subgroup (alternatingGroup (Fin 6))) := by
    intro hh
    rw [hh,relIndex_self] at hiB
    contradiction
  have hBc := (Theory.SpecificGroups.SymplecticFour.Binary.ComponentActionGeometry.sylow_overgroup_cases
    (MulEquiv.refl (alternatingGroup (Fin 6))) P B hPB hbtop).resolve_left hBP
  have hb := (hfix α hα hp).1
  rcases (hall B hBc).mp hPB with hh | hh
  · rw [hh,hJ] at hb
    exact hne hb.symm
  · rw [hh,hL] at hb
    exact hne hb

private def a6ComponentImageEquiv
    (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    (K ⧸ pCore 2 K) ≃* actorImage H K :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)

private theorem marked_a6_image_action
    (H K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (j : actorImage H K ≃* alternatingGroup (Fin 6))
    (s : H) (hs : (s:G) ∈ normalizer (K : Set G))
    (hsD : QuotientGroup.mk' (pCore 2 H) s ∈ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) :
    markedCoreAction 2 K ((a6ComponentImageEquiv H K hKH hK).trans j) ⟨s,hs⟩ =
      MulAut.congr j ((actorImage H K).normalizerMonoidHom
        ⟨QuotientGroup.mk' (pCore 2 H) s,hsD⟩) := by
  let c := a6ComponentImageEquiv H K hKH hK
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := (c.trans j).surjective x
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
  rw [markedCoreAction_mk]
  change j (c _) = j ((actorImage H K).normalizerMonoidHom _
    (j.symm (j (c (QuotientGroup.mk' (pCore 2 K) k)))))
  rw [j.symm_apply_apply]
  apply congrArg j
  apply Subtype.ext
  change QuotientGroup.mk' (pCore 2 H) (s * ⟨k,hKH k.property⟩ * s⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  rfl

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv

theorem source_normal_a6_seed_stabilizer_index
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)) :
    let W := (originalSection a).subspacePreimage I
    (∃ s : T, (s:G) ∉ normalizer (W : Set G)) ∧
      (normalizer (W : Set G)).relIndex (T : Subgroup G) = 2 := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let W := (originalSection a).subspacePreimage I
  let D := actorImage Mc K
  let : D.Normal := hnK.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  let P := actorImage Mc T ⊓ normalizer (D : Set (Mc ⧸ pCore 2 Mc))
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let eK := (a6ComponentImageEquiv Mc K hKM hK).trans b.groupEquiv
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  obtain ⟨R,hR,J,L,hJ,hL,hne,hi,hall,s,hsJ,hsL⟩ :=
    source_normal_a6_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv
      Mc hout K hKM hK hnK eK
  let Rq := R.mapSurjective (f := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
    (eK.surjective.comp (QuotientGroup.mk'_surjective _))
  let sh : Mc := ⟨s,hout.1.2 s.property⟩
  have hsP : q sh ∈ P := ⟨⟨sh,s.property,rfl⟩, by rw [normalizer_eq_top]; trivial⟩
  have hn : (s:G) ∉ normalizer (W : Set G) := by
    intro hh
    have hm := ((originalSection a).mem_normalizer_subspacePreimage_iff I sh).mp hh
    have hnat := hI.alternating_six_natural_of_map_eq a.representation ⟨q sh,hsP⟩
      b.groupEquiv b.linearEquiv b.intertwines hm
    have hmark := marked_a6_image_action Mc K hKM hK b.groupEquiv sh (hTK s.property) hsP.2
    exact swap_not_natural Rq J L hi hne hall _ hsJ hsL (hmark ▸ hnat)
  refine ⟨⟨s,hn⟩,?_⟩
  have hidx := hI.alternating_six_stabilizer_index a.representation
    b.groupEquiv b.linearEquiv b.intertwines ⟨⟨q sh,hsP⟩,fun hh => hn
      (((originalSection a).mem_normalizer_subspacePreimage_iff I sh).mpr hh)⟩
  have hN : (normalizer (W : Set G)).subgroupOf Mc =
      (subspaceStabilizer a.representation I).comap q := by
    ext x
    change (x:G) ∈ normalizer (W : Set G) ↔ q x ∈ subspaceStabilizer a.representation I
    rw [(originalSection a).mem_normalizer_subspacePreimage_iff I x]
    exact subspace_map_eq_iff a.representation I (q x)
  rw [←relIndex_subgroupOf (H := normalizer (W : Set G)) hout.1.2,hN,relIndex_comap]
  change (subspaceStabilizer a.representation I).relIndex (actorImage Mc T) = 2
  simpa only [normalizer_eq_top,inf_top_eq] using hidx

/-- In the single normal A₆ branch the seed stabilizer already has the
literal local normalizer needed in U3. The central cover need not split. -/
theorem source_normal_a6_seed_geometry
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hnK : (K.subgroupOf Mc).Normal) (hgen : K ⊔ (T : Subgroup G) = Mc)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc)))}
    (hI : IsIrrPlusWith a.representation (actorImage Mc K)
      (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)) :
    let W := (originalSection a).subspacePreimage I
    CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W
      ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  let W := (originalSection a).subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (W : Set G)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hnK)
  have hindex : S.relIndex (T : Subgroup G) = 2 := by
    have hh := (source_normal_a6_seed_stabilizer_index hG T hempty hM hunique hmany hcard e hab hsolv
      K hKM hK hnK a hI b).2
    exact (inf_relIndex_left (T : Subgroup G) (normalizer (W : Set G))).trans hh
  obtain ⟨hz,hle,hKW,hN,hsep⟩ := source_component_seed_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI.isIrrPlus
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hSM : S ≤ Mc := hST.trans hout.1.2
  let P := T.subtype hout.1.2
  let R := K.subgroupOf Mc
  let B := S.subgroupOf Mc
  let : R.Normal := hnK
  have hgen' : R ⊔ (P : Subgroup Mc) = ⊤ := by
    rw [show (P : Subgroup Mc) = (T : Subgroup G).subgroupOf Mc from rfl,
      ←subgroupOf_sup hKM hout.1.2,hgen,subgroupOf_self]
  let ec := (cComponentTwoCoreQuotientEquiv hK).trans b.groupEquiv
  let f := ec.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := ec.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ ec.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hself : ∀ Q : Sylow 2 R, normalizer (Q : Set R) = Q :=
    Sylow.self_normalizing_of_two_kernel f hf hk AlternatingSix.ShadowLocal.sylow_normalizer_eq
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp (normal_of_index_eq_two hindex)
  have hBN : normalizer (B : Set Mc) = (P : Subgroup Mc) := by
    apply P.normalizer_subgroup_eq_of_normal_supplement R hgen' hself B
      (fun _ hx => hST hx)
    · intro x hx
      exact ⟨hx.1,hKW hx.2⟩
    · intro x hx
      rw [←subgroupOf_normalizer_eq hSM]
      exact hTS hx
  have hlocal : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
    have hn : (normalizer (S : Set G)).subgroupOf Mc = (T : Subgroup G).subgroupOf Mc := by
      rw [subgroupOf_normalizer_eq hSM]
      exact hBN
    have hh := congrArg (Subgroup.map Mc.subtype) hn
    rw [map_subgroupOf_eq_of_le hout.1.2,subgroupOf_map_subtype] at hh
    exact (inf_comm Mc (normalizer (S : Set G))).trans hh
  refine ⟨source_component_fitting_placement hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK,(originalSection a).subspacePreimage_le I,hz,hKW,hST,hindex,hlocal,?_⟩
  intro t ht hnt
  exact hsep t ht (hTK ht) (fun hn => hnt ⟨ht,hn⟩)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
