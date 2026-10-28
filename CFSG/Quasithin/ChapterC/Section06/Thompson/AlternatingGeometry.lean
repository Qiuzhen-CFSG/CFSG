module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingKernel
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.FourGeometry
public import Theory.GroupTheory.ElementaryThompsonFourFamilyTransport
/-!
# The original A₅ four-family geometry

Restrict the source permutation action to Baum(R), retaining its literal core,
central factor and opposite module. The fixed profile and binary coordinates
produce the elementary square and its two distinct crossing commutators.
The subgroup inclusion transports all of these facts to the original group.

Source: Aschbacher–Smith C.6.1, printed p.165, from the C.5.6 source family.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

omit [Finite G] in
private theorem restrict_image (S N B : Subgroup G) (hSN : S ≤ N) (hBS : B ≤ S)
    (a : N →* FivePerm) :
    (B.subgroupOf S).map (a.comp (inclusion hSN)) = (B.subgroupOf N).map a := by
  ext p
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨inclusion hSN b,hb,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b,hBS hb⟩,hb,rfl⟩

theorem AlternatingPairSetup.four_geometry
    (h : AlternatingPairSetup R K L)
    (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (hphi : let D := ChapterB.baumann R ⊓ centralizer (K : Set G)
      (frattini D).map D.subtype = ⊥) :
    let S := ChapterB.baumann R
    let Q := (K ⊔ S).pCoreIn 2
    let W := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (S ⊓ centralizer (K : Set G))
    ∃ P P' : Subgroup G,
      elementaryAbelianMaxSubgroups R = {Q,W,P,P'} ∧
      actionImage h.action P = line 0 ∧ actionImage h.action P' = line 1 ∧
      FourFamilyGeometry S Q W P P' (Q ⊓ W) := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let D := S ⊓ centralizer (K : Set G)
  let Q := (K ⊔ S).pCoreIn 2
  let W := U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ D
  let σ := h.action.comp (inclusion (show S ≤ K ⊔ S from le_sup_right))
  have hUS : U ≤ S := h.module_le
  have hDS : D ≤ S := inf_le_left
  have hQS : Q ≤ S := h.core.le.trans inf_le_left
  have hVS : U.map (MulAut.conj x⁻¹).toMonoidHom ≤ S :=
    (map_mono hUS).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx)))
  have hWS : W ≤ S := sup_le hVS hDS
  let Ui := U.subgroupOf S
  let Di := D.subgroupOf S
  let Qi := Q.subgroupOf S
  let Wi := W.subgroupOf S
  obtain ⟨P,P',hf,hPmap,hP'map⟩ := h.intrinsic_family_eq_four x hx hnc hphi
  change elementaryAbelianMaxSubgroups (⊤ : Subgroup S) = {Qi,Wi,P,P'} at hf
  have hW : Wi ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hf]; simp
  have hP : P ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hf]; simp
  have hP' : P' ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hf]; simp
  have hk : σ.ker = Qi := by
    ext s
    change h.action (inclusion le_sup_right s) = 1 ↔ (s : G) ∈ Q
    change inclusion le_sup_right s ∈ h.action.ker ↔ _
    rw [h.action_kernel]
    change (s : G) ∈ centralizer (U : Set G) ↔ (s : G) ∈ Q
    rw [show Q = S ⊓ centralizer (U : Set G) from h.core]
    exact (and_iff_right s.property).symm
  have hr : σ.range = ChapterB.Offenders.D 5 := by
    have hh := restrict_image S (K ⊔ S) S le_sup_right le_rfl h.action
    rw [subgroupOf_self,←MonoidHom.range_eq_map] at hh
    exact hh.trans h.baumann_image
  have hWmap : Wi.map σ = ChapterB.Offenders.D 5 := by
    rw [restrict_image S (K ⊔ S) W le_sup_right hWS h.action]
    rw [show W = U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ D from rfl,
      subgroupOf_sup (hVS.trans le_sup_right) (hDS.trans le_sup_right),Subgroup.map_sup]
    have hd : (D.subgroupOf (K ⊔ S)).map h.action = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      intro d hd
      rw [h.action_kernel]
      exact (inf_le_right.trans (centralizer_le (map_subtype_le _))) hd
    rw [hd,sup_bot_eq]
    exact h.conjugate_action_image x hx hnc
  let : IsElementaryAbelian 2 Q := (h.elementary_factor_pair x hx hnc hphi).1
  let : IsElementaryAbelian 2 Qi := IsElementaryAbelian.subgroupOf hQS
  have hprod : Qi = Ui ⊔ Di := by
    change Q.subgroupOf S = _
    rw [show Q = U ⊔ D from h.product,subgroupOf_sup hUS hDS]
  have hDcentral := (h.elementary_factor_pair x hx hnc hphi).2.2.2
  have hDi : Di ≤ center S := by
    intro d hd
    exact mem_center_iff.mpr (fun s => Subtype.ext (hDcentral hd s s.property))
  let e : Ui ≃* Multiplicative Vector := (subgroupOfEquivOfLe hUS).trans h.coordinates
  let ι : Multiplicative Vector →* S := Ui.subtype.comp e.symm.toMonoidHom
  have hi : Function.Injective ι := Ui.subtype_injective.comp e.symm.injective
  have hir : ι.range = Ui := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have he (s : S) (v : Vector) :
      ι (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) (σ s) v)) =
        s * ι (Multiplicative.ofAdd v) * s⁻¹ := by
    apply Subtype.ext
    have hh := h.equivariant (inclusion le_sup_right s) (h.coordinates.symm (Multiplicative.ofAdd v))
    simpa [ι,e,σ,subgroupOfEquivOfLe] using hh
  have hnorm (B : Subgroup S) (hB : B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S)) :
      (⊤ : Subgroup S) ≤ normalizer (B : Set S) := by
    have hb : B.map S.subtype ∈ elementaryAbelianMaxSubgroups R := by
      rw [←baumann_maxFamily R]
      have hm := (maxFamily_map_injective_iff S.subtype S.subtype_injective ⊤ B).mpr hB
      simpa only [←MonoidHom.range_eq_map,range_subtype] using hm
    have hn := h.baumann_normalizes_max_family x hx hnc hphi (B.map S.subtype) hb
    intro s _
    have hh := hn s.property
    have hh' : s ∈ (normalizer (B.map S.subtype : Set G)).subgroupOf S := hh
    rw [subgroupOf_normalizer_eq (map_subtype_le B),subgroupOf,comap_map_eq_self_of_injective S.subtype_injective] at hh'
    exact hh'
  have hQi : Qi ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup S) := by rw [hf]; simp
  have hg := marked_four_geometry σ Qi Wi P P' Di hk hr
    (h.intrinsic_fixedProfile x hx hnc hphi) hW hP hP' hWmap hPmap hP'map
    (le_top.trans (hnorm Wi hW)) (le_top.trans (hnorm Qi hQi)) ι hi
    (hir.symm ▸ hprod) hDi he
  have hga := hg.map_subtype S Qi Wi P P' (Qi ⊓ Wi)
  rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hWS,
    Subgroup.map_inf _ _ _ S.subtype_injective,map_subgroupOf_eq_of_le hQS,
    map_subgroupOf_eq_of_le hWS] at hga
  refine ⟨P.map S.subtype,P'.map S.subtype,?_,?_,?_,hga⟩
  · ext B
    rw [←baumann_maxFamily R,maxFamily_equiv_iff S (MulEquiv.refl S) B,hf]
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,exists_eq_or_imp,exists_eq_left]
    change (B = Qi.map S.subtype ∨ B = Wi.map S.subtype ∨ B = P.map S.subtype ∨ B = P'.map S.subtype) ↔ _
    rw [map_subgroupOf_eq_of_le hQS,map_subgroupOf_eq_of_le hWS]
  · change ((P.map S.subtype).subgroupOf (K ⊔ S)).map h.action = line 0
    rw [←restrict_image S (K ⊔ S) (P.map S.subtype) le_sup_right (map_subtype_le P) h.action,
      subgroupOf,comap_map_eq_self_of_injective S.subtype_injective]
    exact hPmap
  · change ((P'.map S.subtype).subgroupOf (K ⊔ S)).map h.action = line 1
    rw [←restrict_image S (K ⊔ S) (P'.map S.subtype) le_sup_right (map_subtype_le P') h.action,
      subgroupOf,comap_map_eq_self_of_injective S.subtype_injective]
    exact hP'map
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
