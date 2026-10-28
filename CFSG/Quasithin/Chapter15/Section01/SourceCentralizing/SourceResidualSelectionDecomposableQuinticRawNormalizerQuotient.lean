module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawNormalizer
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# The literal normalizer quotient and its proper marked Sylow image

The reduced original-seed action kills O₂(L). Its actual map to the image
therefore factors through L/O₂(L), with central kernel. The seed remains
inside its normal closure, so the action kernel lies in the original marked
local. Its marked image is proper and contains the original Sylow image.
All maps retain their value on every original element of L.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original constrained component has the genuine central comparison
and proper marked overgroup in its original normalizer-action image. -/
theorem PreparedChosenModule.raw_component_normalizer_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hL : L ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hfit : generalizedFitting L = pCore 2 L)
    (houtMZ : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (houtM : ¬L ≤ M) :
    let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
    let R := S ⊓ normalizer (L : Set G)
    let H := L ⊔ R
    let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
    let C := centralizer (W : Set H)
    let q := QuotientGroup.mk' C
    let K := (L.subgroupOf H).map q
    let MZ := centralizer (Z1 : Set G) ⊓ Mc
    ∃ (f : L →* K) (e : (L ⧸ pCore 2 L) →* K),
      (∀ x : L, (f x : H ⧸ C) = q (inclusion le_sup_left x)) ∧
      (∀ x : L, e (QuotientGroup.mk' (pCore 2 L) x) = f x) ∧
      Function.Surjective f ∧ Function.Surjective e ∧
      e.ker ≤ center (L ⧸ pCore 2 L) ∧
      Nonempty ((L ⧸ centralPreimage (pCore 2 L)) ≃* (K ⧸ center K)) ∧
      ((MZ.subgroupOf L).map f).comap f = MZ.subgroupOf L ∧
      (MZ.subgroupOf L).map f ≠ ⊤ ∧
      ∃ P : Sylow 2 K,
        (P : Subgroup K) = ((S ⊓ L).subgroupOf L).map f ∧
        (P : Subgroup K) ≤ (MZ.subgroupOf L).map f := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  let R := S ⊓ normalizer (L : Set G)
  let H := L ⊔ R
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let K := (L.subgroupOf H).map q
  let MZ := centralizer (Z1 : Set G) ⊓ Mc
  obtain ⟨hr,_,_,hquasi,_,_,_⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hL hq hfit houtMZ houtM
  have hZR := (h.raw_component_thompson hG T hM hJ hu hZ hL hq hfit houtMZ houtM).2.2.2.2
  let f : L →* K := (q.comp (inclusion le_sup_left)).codRestrict _
    (fun x => mem_map_of_mem q (show inclusion le_sup_left x ∈ L.subgroupOf H from x.property))
  have hf : Function.Surjective f := by
    rintro ⟨_,⟨x,hx,rfl⟩⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hcore : pCore 2 L ≤ f.ker := by
    have hh : L.pCoreIn 2 ≤ H.pCoreIn 2 := pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer inf_le_right)
    intro x hx
    obtain ⟨y,hy,he⟩ := hh (mem_map_of_mem L.subtype hx)
    have he' : y = inclusion (show L ≤ H from le_sup_left) x := Subtype.ext he
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    exact le_centralizer_iff.mp hr.le_centralizer_pCore (he' ▸ hy)
  let e : (L ⧸ pCore 2 L) →* K := QuotientGroup.lift _ f hcore
  have he : Function.Surjective e := QuotientGroup.lift_surjective_of_surjective _ _ hf _
  let := hq
  let : IsQuasisimple K := hquasi
  have hcentral : e.ker ≤ center (L ⧸ pCore 2 L) :=
    (show Covering (L ⧸ pCore 2 L) K from
      { toMonoidHom := e, surjective := he }).ker_le_center
  let cover : PerfectCentralCovering.Cover (L ⧸ pCore 2 L) K :=
    { toMonoidHom := e, surjective := he,
      isPerfect := hq.toIsPerfect, ker_le_center := hcentral }
  have hk : ((QuotientGroup.mk' (center K)).comp f).ker =
      centralPreimage (pCore 2 L) := by
    ext x
    change QuotientGroup.mk' (center K) (f x) = 1 ↔ _
    exact (QuotientGroup.eq_one_iff (f x)).trans
      (SetLike.ext_iff.mp cover.comap_center (QuotientGroup.mk' (pCore 2 L) x))
  have hquot : Nonempty ((L ⧸ centralPreimage (pCore 2 L)) ≃* (K ⧸ center K)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        ((QuotientGroup.mk' (center K)).comp f)
        ((QuotientGroup.mk'_surjective _).comp hf))⟩
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hCMZ : C.map H.subtype ≤ MZ := by
    rintro _ ⟨x,hx,rfl⟩
    refine ⟨(sup_le hL.1 (inf_le_left.trans inf_le_right)) x.property,hMc.2 ?_⟩
    intro z hz
    exact congrArg Subtype.val (hx ⟨z,mem_sup_right (hZR hz)⟩ (le_normalClosure hz))
  have hkerMZ : f.ker ≤ MZ.subgroupOf L := by
    intro x hx
    have heq := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have hc := (QuotientGroup.eq_one_iff _).mp heq
    exact hCMZ (mem_map_of_mem H.subtype hc)
  have hpre : ((MZ.subgroupOf L).map f).comap f = MZ.subgroupOf L :=
    comap_map_eq_self hkerMZ
  have hproper : (MZ.subgroupOf L).map f ≠ ⊤ := by
    intro ht
    have hh := hpre
    rw [ht,comap_top] at hh
    exact houtMZ (subgroupOf_eq_top.mp hh.symm)
  refine ⟨f,e,fun _ => rfl,fun _ => rfl,hf,he,hcentral,hquot,hpre,hproper,?_⟩
  obtain ⟨P,hP⟩ := ComponentModels.source20_sylow_intersection hL.2
  have hPe : (P : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le inf_le_right]
  refine ⟨P.mapSurjective hf,?_,?_⟩
  · change (P : Subgroup L).map f = _
    rw [hPe]
  · change (P : Subgroup L).map f ≤ _
    apply map_mono
    rw [hPe]
    intro x hx
    exact ⟨hx.1.2,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x hx.1.1).symm)⟩

end CFSG.Quasithin.Chapter15.Section01
